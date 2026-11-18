#!/usr/bin/env python3
"""Strict, non-executing evidence adapters. No claim of producer authenticity."""
import argparse
import copy
import hashlib
import json
import pathlib
import reference_kernel as kernel

CONTEXT = {'artifact', 'lineage', 'environment', 'harness', 'workload', 'venue'}

def canonical(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode('ascii')

def digest(x):
    return hashlib.sha256(canonical(x)).hexdigest()

def read(path):
    raw = pathlib.Path(path).read_bytes()
    return raw, json.loads(raw.decode('utf-8'), object_pairs_hook=kernel.unique_object,
                           parse_constant=lambda x: fail('nonfinite JSON number'))

def fail(message):
    raise ValueError(message)

def require(ok, message):
    if not ok: fail(message)

def context(c):
    kernel.fields(c, CONTEXT)
    require(all(type(v) is str and v for v in c.values()), 'invalid context ID')

def validate_authority(a):
    kernel.fields(a, ['schema', 'context', 'model', 'tests', 'benchmarks'])
    require(a['schema'] == 'portable-authority/v1', 'unsupported authority schema')
    context(a['context']); kernel.validate(a['model'])
    require(a['model']['events'] == [], 'authority model must not submit observations')
    for item in a['model']['edges'] + a['model']['tasks']:
        require('context' not in item, 'authority model context must be inherited, not overridden')
    atoms = set(a['model']['atoms'])
    for group in ['tests', 'benchmarks']:
        require(type(a[group]) is dict, 'mapping required')
        kernel.names(list(a[group]))
    for mapping in a['tests'].values():
        kernel.fields(mapping, ['pass', 'fail'])
        require(all(type(x) is str and x in atoms for x in mapping.values()), 'unknown test atom')
        require(mapping['pass'] != mapping['fail'], 'pass/fail atoms must differ')
    require(all(type(x) is str and x in atoms and x == 'measurement:' + key for key,x in a['benchmarks'].items()), 'benchmark atom must be measurement:<subject>')

def import_document(authority, raw):
    validate_authority(authority)
    doc = json.loads(raw.decode('utf-8'), object_pairs_hook=kernel.unique_object,
                     parse_constant=lambda x: fail('nonfinite JSON number'))
    kernel.fields(doc, ['schema', 'context', 'records'])
    context(doc['context']); require(doc['context'] == authority['context'], 'context mismatch')
    require(doc['schema'] in ['ci-results/v1', 'benchmark-samples/v1'], 'unsupported input schema')
    require(type(doc['records']) is list, 'records must be a list')
    seen = set(); receipts = []
    for index, record in enumerate(doc['records']):
        is_test = doc['schema'] == 'ci-results/v1'
        kernel.fields(record, ['subject', 'status'] if is_test else ['subject', 'samples_ns'])
        subject = record['subject']; kernel.names([subject])
        require(subject not in seen, 'duplicate subject within input'); seen.add(subject)
        require(subject in authority['tests' if is_test else 'benchmarks'], 'unknown subject')
        if is_test:
            require(type(record['status']) is str and record['status'] in ['pass','fail','skipped','error'], 'invalid status')
        else:
            samples = record['samples_ns']
            require(type(samples) is list and bool(samples), 'samples required')
            require(all(type(n) is int and n >= 0 for n in samples), 'integer nanoseconds required')
        receipt = {'schema':'portable-receipt/v1', 'kind':'test' if is_test else 'measurement',
                   'classification':'observed', 'context':copy.deepcopy(doc['context']),
                   'subject':subject, 'payload':copy.deepcopy(record),
                   'source_sha256':hashlib.sha256(raw).hexdigest(), 'record_index':index,
                   'authority_sha256':digest(authority)}
        receipt['id'] = 'receipt:' + digest(receipt)
        receipts.append(receipt)
    return receipts

def build(authority, sources, withdrawn=()):
    """Re-import original bytes; callers cannot supply arbitrary fabricated receipts."""
    validate_authority(authority)
    receipts = {}
    for raw in sources:
        for receipt in import_document(authority, raw):
            rid = receipt['id']
            require(rid not in receipts or receipts[rid] == receipt, 'receipt collision')
            receipts[rid] = receipt
    kernel.names(list(withdrawn)); require(set(withdrawn) <= receipts.keys(), 'unknown withdrawal')
    model = copy.deepcopy(authority['model'])
    scoped = {'lineage':authority['context']['lineage'], 'environment':digest(authority['context'])}
    for edge in model['edges']: edge['context'] = scoped.copy()
    for task in model['tasks']: task['context'] = scoped.copy()
    for rid, r in sorted(receipts.items()):
        atom = None
        if r['kind'] == 'measurement': atom = authority['benchmarks'][r['subject']]
        elif r['payload']['status'] in ['pass','fail']:
            atom = authority['tests'][r['subject']][r['payload']['status']]
        if atom is not None:
            model['events'].append({'id':rid,'type':'observe','atom':atom,'context':scoped.copy()})
            if rid in withdrawn:
                model['events'].append({'id':'withdraw:'+digest(rid),'type':'withdraw','target':rid})
    kernel.validate(model)
    result = {'schema':'portable-projection/v1', 'authority_sha256':digest(authority),
              'context':authority['context'], 'kernel_context':scoped,
              'observed_receipts':[receipts[k] for k in sorted(receipts)],
              'withdrawn_receipts':sorted(withdrawn), 'normalized_hypergraph':model,
              'inferred_view':kernel.derive(model,scoped), 'incidence':kernel.incidence(model),
              'proposed_tasks':model['tasks']}
    result['projection_sha256'] = digest(result)
    return result

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('authority'); p.add_argument('inputs', nargs='+'); p.add_argument('--withdraw', action='append', default=[])
    args = p.parse_args()
    try:
        _, a = read(args.authority)
        print(json.dumps(build(a, [pathlib.Path(f).read_bytes() for f in args.inputs], args.withdraw), sort_keys=True, indent=2))
    except (ValueError, KeyError, TypeError, UnicodeError, OSError) as e:
        p.exit(2, 'refused: '+str(e)+'\n')
if __name__ == '__main__': main()
