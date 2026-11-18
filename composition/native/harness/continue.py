from pathlib import Path
import time,os,signal,json
p=Path('/workspace/home/identity'); runner=1064; compiler=1077
r=json.loads((p/'continuation.json').read_text())
try:
 while time.time()<r['deadline']:
  q=Path('/proc/'+str(compiler)+'/stat')
  if not q.exists() or q.read_text().split()[2]=='Z':break
  time.sleep(1)
 r['finished_at']=time.time();q=Path('/proc/'+str(compiler)+'/stat');r['compiler_finished']=not q.exists() or q.read_text().split()[2]=='Z'
finally:
 os.kill(runner,signal.SIGCONT)
 r['supervisor_resumed']=True
 (p/'continuation.json').write_text(json.dumps(r,indent=2)+'\n')
