from pathlib import Path
import subprocess, json, hashlib, time, os, signal, platform, resource
base=Path("/workspace/home/identity")
repo=base/"idol"
out=base/"results-runtime"
art=base/"artifacts"
out.mkdir(exist_ok=True)
art.mkdir(exist_ok=True)
zig=base/"zig-x86_64-linux-0.17.0-dev.1567+f0354179a"/"zig"
records=[]
def invoke(name,args,limit=600,cwd=repo,env=None,required=True):
    log=out/(name+".log")
    start=time.monotonic()
    with log.open("wb") as stream:
        process=subprocess.Popen([str(x) for x in args],cwd=cwd,stdin=subprocess.DEVNULL,stdout=stream,stderr=subprocess.STDOUT,env=env,start_new_session=True)
        timedout=False
        try:
            code=process.wait(timeout=limit)
        except subprocess.TimeoutExpired:
            timedout=True
            os.killpg(process.pid,signal.SIGTERM)
            try: code=process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid,signal.SIGKILL)
                code=process.wait()
    data=log.read_bytes()
    record={"name":name,"command":[str(x) for x in args],"cwd":str(cwd),"exit":code,"timeout":timedout,"seconds":time.monotonic()-start,"log_sha256":hashlib.sha256(data).hexdigest(),"bytes":len(data),"output":data.decode(errors="replace")}
    records.append(record)
    (out/(name+".json")).write_text(json.dumps(record,indent=2)+"\n")
    (out/"runs.json").write_text(json.dumps(records,indent=2)+"\n")
    print(json.dumps({k:v for k,v in record.items() if k not in ["output","command"]}),flush=True)
    if required and code!=0: raise RuntimeError(name+" failed")
    return record
def artifact(path):
    data=path.read_bytes()
    record={"path":str(path),"bytes":len(data),"sha256":hashlib.sha256(data).hexdigest(),"elf_machine":int.from_bytes(data[18:20],"little") if data[:4]==b"\x7fELF" else None}
    (out/(path.name+".artifact.json")).write_text(json.dumps(record,indent=2)+"\n")
    return record
empty=art/"empty.o";empty.write_bytes(b"")
projection=art/"io.zig"
projection.write_text("pub const Symbol = struct { name: []const u8, at: usize, arity: u32 };\npub const Relocation = struct { at: usize, section: enum { text, read, data }, offset: usize };\npub const code: []const u8 = &.{};\npub const read: []const u8 = &.{};\npub const symbols: []const Symbol = &.{};\npub const relocations: []const Relocation = &.{};\npub const data_size: usize = 0;\npub const startup: ?usize = null;\n")
def compiler(name,io,start,strings,errno,keyword):
    deps={"x86.io":projection,"strruntime.id":repo/"lib/runtime/strruntime.id","exit":repo/"src/polyglot/exit.zig","idol_io_runtime.o":io,"idol_str_runtime.o":strings,"idol_errno_runtime.o":errno,"idol_start_runtime.o":start,"keyword_classify.o":keyword}
    command=["qemu-x86_64",zig,"build-exe","-j2","-ODebug","-target","aarch64-linux-gnu","-fno-lld","--gc-sections","-fstrip","--libc",base/"libc.conf"]
    command += [str(art/(part+".o")) for part in ["lexer","parser","case"]]
    for dep in deps: command += ["--dep",dep]
    command += ["-Mroot=src/main.zig"]
    for dep,path in deps.items(): command += ["-M"+dep+"="+str(path)]
    command += ["-lc","-femit-bin="+str(art/name)]
    result=invoke("build-"+name,command,limit=780)
    info=artifact(art/name)
    if info["elf_machine"]!=183: raise RuntimeError("Not native ARM compiler")
    (art/(name+".digest")).write_text(info["sha256"]+"\n")
    return art/name

import sys
invoke("io-object",["qemu-x86_64",zig,"build-obj","src/idol_io_runtime.zig","-target","aarch64-linux-gnu","-OReleaseFast","-fstrip","-fno-lld","--libc",base/"libc.conf","-lc","-femit-bin="+str(art/"io.o")],limit=40)
invoke("start-object",["qemu-x86_64",zig,"build-obj","src/idol_start_runtime.zig","-target","aarch64-linux-gnu","-OReleaseFast","-fstrip","-fno-lld","-femit-bin="+str(art/"start.o")],limit=40)
invoke("keyword-object",["gcc","-c","-std=c11","-O2","-g0","-ffunction-sections","-fdata-sections","-w","src/keyword_classify.c","-o",art/"keyword.o"],limit=10)
for n in ["io.o","start.o","keyword.o","str.o","errno.o"]:artifact(art/n)
os.execv(sys.executable,[sys.executable,str(base/"run-objects.py")])
