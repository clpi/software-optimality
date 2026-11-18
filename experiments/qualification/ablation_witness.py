import json, os
items=[]; outcomes=[]
def pytest_collection_modifyitems(session, config, items):
    if os.environ.get('REVERSE_TESTS') == '1': items.reverse()
    globals()['items']=[x.nodeid for x in items]
def pytest_runtest_logreport(report):
    outcomes.append({'nodeid':report.nodeid,'phase':report.when,'outcome':report.outcome,'skip_reason':str(report.longrepr) if report.skipped else None})
def pytest_sessionfinish(session, exitstatus):
    with open(os.environ['WITNESS_PATH'],'w') as f: json.dump({'items':items,'outcomes':outcomes,'exitstatus':int(exitstatus)},f)
