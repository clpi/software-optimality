#!/usr/bin/env python3
"""Validated measurement-only bridge: count then one integer nanosecond per line."""
import sys
from pathlib import Path
import pipeline as p
if __name__ == '__main__':
    _, authority = p.read(sys.argv[1])
    receipts = p.import_document(authority, Path(sys.argv[2]).read_bytes())
    samples = [n for r in receipts if r['kind']=='measurement' for n in r['payload']['samples_ns']]
    # Fixed-width C bridge refuses values it cannot preserve; Python retains full integers.
    p.require(all(n <= 2**64-1 for n in samples), 'sample outside C uint64 range')
    print(len(samples))
    for n in samples: print(n)
