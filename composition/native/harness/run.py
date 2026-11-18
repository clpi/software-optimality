from pathlib import Path
import subprocess, json, hashlib, time, os, signal, platform, resource
base=Path("/workspace/home/identity")
repo=base/"idol"
out=base/"results"
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
    command=["qemu-x86_64",zig,"build-exe","-j2","-ODebug","-target","aarch64-linux-gnu","-fno-lld","--gc-sections"]
    command += [str(art/(part+".o")) for part in ["lexer","parser","case"]]
    for dep in deps: command += ["--dep",dep]
    command += ["-Mroot=src/main.zig"]
    for dep,path in deps.items(): command += ["-M"+dep+"="+str(path)]
    command += ["-lc","-femit-bin="+str(art/name)]
    result=invoke("build-"+name,command,limit=600)
    info=artifact(art/name)
    if info["elf_machine"]!=183: raise RuntimeError("Not native ARM compiler")
    (art/(name+".digest")).write_text(info["sha256"]+"\n")
    return art/name
try:
    environment={"machine":platform.machine(),"cpu":Path("/sys/fs/cgroup/cpu.max").read_text().strip(),"memory":Path("/sys/fs/cgroup/memory.max").read_text().strip(),"source_commit":"ef3dbcfa847579df2c839bb73240242fe5ebdd4e","source_tree":"fffa952f1042e559441ef8cf252b847c3a3e7f02","source_archive_sha256":hashlib.sha256((base/"source.tar.xz").read_bytes()).hexdigest()}
    (out/"environment.json").write_text(json.dumps(environment,indent=2)+"\n")
    invoke("gcc-version",["gcc","--version"],limit=10)
    invoke("zig-version",["qemu-x86_64",zig,"version"],limit=10)
    invoke("lexer-object",["gcc","-c","-std=c11","-w","-Dmain=idol_lexer_tokenize_main","src/lexer_tokenize.c","-o",art/"lexer.o"],limit=180)
    invoke("parser-object",["gcc","-c","-std=c11","-O2","-g0","-ffunction-sections","-fdata-sections","-w","-Dmain=idol_parser_projection_main","-Dis_digit=idol_parser_is_digit","-Dduo_u_isdigit=idol_parser_isdigit","-Dboundary(...)=idol_parser_boundary(__VA_ARGS__)","-Devent(...)=idol_parser_event(__VA_ARGS__)","-Dfieldstart(...)=idol_parser_fieldstart(__VA_ARGS__)","src/parser/projection.c","-o",art/"parser.o"],limit=180)
    invoke("case-object",["gcc","-c","-std=c11","-O2","-g0","-ffunction-sections","-fdata-sections","-w","-Dmain=idol_case_decide_main","-Ddecidecase(...)=idol_case_decide(__VA_ARGS__)","src/case.c","-o",art/"case.o"],limit=180)
    seed=compiler("idol-seed",empty,empty,empty,empty,empty)
    invoke("seed-authority",[seed,"authority"],limit=30)
    invoke("strings",[seed,"compile","--no-cache","--backend=direct","--emit","obj","--build-report=plain","lib/runtime/strruntime.id","-o",art/"str.o"],limit=240)
    invoke("errno",[seed,"compile","--no-cache","--backend=direct","--emit","obj","--build-report=plain","lib/os/linux/errno.id","-o",art/"errno.o"],limit=120)
    invoke("io-object",["qemu-x86_64",zig,"build-obj","src/idol_io_runtime.zig","-target","aarch64-linux-gnu","-OReleaseFast","-fstrip","-lc","-femit-bin="+str(art/"io.o")],limit=120)
    invoke("start-object",["qemu-x86_64",zig,"build-obj","src/idol_start_runtime.zig","-target","aarch64-linux-gnu","-OReleaseFast","-fstrip","-femit-bin="+str(art/"start.o")],limit=120)
    invoke("keyword-object",["gcc","-c","-std=c11","-O2","-g0","-ffunction-sections","-fdata-sections","-w","src/keyword_classify.c","-o",art/"keyword.o"],limit=60)
    idol=compiler("idol",art/"io.o",art/"start.o",art/"str.o",art/"errno.o",art/"keyword.o")
    invoke("authority",[idol,"authority"],limit=30)
    for label,path in [("identity","test/compiler/identity.id"),("topology","test/compiler/topology.id"),("effects","lib/compiler/self/host/tests/effects.id"),("graph","lib/compiler/self/host/tests/graph.id"),("policy","lib/compiler/self/host/tests/policy.id"),("policycone","lib/compiler/self/host/tests/policycone.id")]:
        binary=art/(label+".test")
        result=invoke(label+"-compile",[idol,"compile","--no-cache","--backend=direct",path,"-o",binary],limit=300,required=False)
        if result["exit"]==0:
            info=artifact(binary)
            if info["elf_machine"]!=183: raise RuntimeError("Not native ARM test")
            invoke(label+"-native",[binary],limit=180,required=False)
    (out/"completed.json").write_text(json.dumps({"status":"COMPLETED","tests_reached":True})+"\n")
except Exception as e:
    (out/"completed.json").write_text(json.dumps({"status":"FAILED","reason":str(e)})+"\n")
    raise
