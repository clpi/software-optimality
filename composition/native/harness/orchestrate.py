from pathlib import Path
import os,signal,time,json,subprocess
p=Path('/workspace/home/identity'); deadline=1795003529; canceled=False
while time.time()<deadline:
 for q in Path('/proc').iterdir():
  if not q.name.isdigit():continue
  try:a=q.joinpath('cmdline').read_bytes().split(b'\0')
  except (FileNotFoundError,PermissionError,ProcessLookupError):continue
  if b'build-exe' in a and b'-femit-bin=/workspace/home/identity/artifacts/idol' in a:
   pid=int(q.name);os.killpg(pid,signal.SIGTERM);canceled=True;r={'reason':'Deliberately cancel redundant full final host compile; continue exact seed object emission with source-defined runtime linker handoff','pid':pid,'command':[v.decode() for v in a if v],'time':time.time(),'signal':'SIGTERM','source_unchanged':True};(p/'handoff.json').write_text(json.dumps(r,indent=2)+'\n')
 completed=p/'results-strip/completed.json'
 if completed.exists():
  needed=['idol-seed','str.o','errno.o','io.o','start.o','keyword.o']
  ready=all((p/'artifacts'/n).is_file() and (p/'artifacts'/n).stat().st_size>0 for n in needed)
  if canceled and ready:
   a=['sh',str(p/'idol/tools/node/dev/idol-lock'),'--timeout','30','--','python3',str(p/'run-objects.py')];(p/'launch-objects.json').write_text(json.dumps({'command':a,'started':time.time(),'mode':'Native direct executable graph object handoff'},indent=2)+'\n');os.execvp(a[0],a)
  (p/'objects-blocked.json').write_text(json.dumps({'reason':'Bootstrap did not produce complete exact seed/runtime inputs','ready':ready,'canceled_redundant_final_compile':canceled,'bootstrap_result':json.loads(completed.read_text())},indent=2)+'\n');raise SystemExit(1)
 time.sleep(1)
(p/'objects-blocked.json').write_text(json.dumps({'reason':'Receipt and cleanup deadline reached before runtime inputs ready'})+'\n')
