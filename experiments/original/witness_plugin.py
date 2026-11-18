import json, os
items=[]; outcomes=[]
def pytest_collection_modifyitems(session, config, items):
    if os.environ.get('REVERSE_TESTS') == '1': items.reverse()
    globals()['items'] = [x.nodeid for x in items]
def pytest_runtest_logreport(report):
    if report.when == 'call' or report.failed or report.skipped:
        outcomes.append([report.nodeid,report.when,report.outcome])
def pytest_sessionfinish(session, exitstatus):
    with open(os.environ['WITNESS_PATH'],'w') as f:
        json.dump({'items':items,'outcomes':outcomes,'exitstatus':int(exitstatus)},f)
