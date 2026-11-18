from pathlib import Path
import time,os,signal,json
p=Path('/workspace/home/identity');deadline=1795003529
while time.time()<deadline:time.sleep(min(2,deadline-time.time()))
killed=[]
for q in Path('/proc').iterdir():
 if not q.name.isdigit():continue
 try:
  st=q.joinpath('stat').read_text().split();a=q.joinpath('cmdline').read_bytes().split(b'\0')
 except (FileNotFoundError,PermissionError,ProcessLookupError):continue
 if int(st[3])==1243:
  pid=int(q.name)
  if int(st[4])!=pid:continue
  os.killpg(pid,signal.SIGTERM);killed.append({'pid':pid,'command':[v.decode() for v in a if v]})
(p/'deadline.json').write_text(json.dumps({'deadline':deadline,'time':time.time(),'reason':'Preserve at least180s for receipt transfer and explicit sandbox deletion','terminated_bootstrap_children':killed},indent=2)+'\n')
