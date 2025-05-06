#!/usr/bin/python

import tempfile
import subprocess
import perfcounters as perf
import args
import os
import signal
import sys

args.argparser.add_argument("--cbmc", default="cbmc", type=str,
    help="path to CBMC")
args.argparser.add_argument("--gcc", default="gcc", type=str,
    help="path to GCC")
args.argparser.add_argument("--gpp", default="g++", type=str,
    help="path to G++")
args.argparser.add_argument("--z3", default=False, type=bool,
    help="use Z3 as the backend")
args.argparser.add_argument("--interpreter", "-I", default="interpreter",
    type=str, help="path to interpreter")
args.argparser.add_argument("--lib", default="lib",
    type=str, help="path to library")
args.argparser.add_argument("--searcher", default="searcher",
    type=str, help="path to searcher")
args.argparser.add_argument("--keeptemps", "-k", default=False,
    action="store_const", const=True,
    help="keep temporary files")
args.argparser.add_argument("--noslice", default=False,
    action="store_const", const=True,
    help="do not slice formula")
args.argparser.add_argument("--strategy",
    choices=["all", "evolve", "explicit", "genetic", "anneal", "cbmc"],
    default="all", help="the overall strategy")
args.argparser.add_argument("--synth-strategy",
    choices=["default", "all", "anneal", "evolve", "explicit", "genetic", "cbmc"],
    default="default", help="the synthesis strategy")
args.argparser.add_argument("--verif-strategy",
    choices=["default", "explicit", "cbmc"], default="default",
    help="the synthesis strategy")
args.argparser.add_argument("--nosymmetry", default=False,
    action="store_const", const=True,
    help="don't add symmetry breakers")
args.argparser.add_argument("--nonops", default=False,
    action="store_const", const=True,
    help="don't add nop breakers")
args.argparser.add_argument("--noconsts", default=False,
    action="store_const", const=True,
    help="don't remove const instructions")
args.argparser.add_argument("--fastverif", default=False, type=bool,
    help="use fast verification")
args.argparser.add_argument("--nondet", default=0, type=int,
    help="number of nondet variables")
args.argparser.add_argument("--maxfit", default=1, type=int,
    help="maximum possible fitness for checkers")
args.argparser.add_argument("--ofiledir", default="/tmp", type=str,
    help="directory to use for object files (must be writable and executable)")

args.argparser.add_argument("-popsize", default=2000, type=int)
args.argparser.add_argument("-keepfrac", default=200, type=int)
args.argparser.add_argument("-newfrac", default=200, type=int)
args.argparser.add_argument("-newsize", default=3, type=int)
args.argparser.add_argument("-tourneysize", default=10, type=int)
args.argparser.add_argument("-mutprob", default=0.01, type=float)
args.argparser.add_argument("-recombprob", default=0.1, type=float)
args.argparser.add_argument("-replaceprob", default=0.1, type=float)


def log2(x):
  i = 0
  extra = 0

  while x > 1:
    if x & 1:
      extra = 1

    x >>= 1
    i += 1

  return i+extra

compiled = {}
geneticsave = tempfile.NamedTemporaryFile(delete=False)

class Checker(object):
  cbmcargs = []
  gccargs = {}
  scratchfile = None

  def __init__(self, sz, width, consts, verif=False):
    nargs = args.args.args
    nres = sz
    nevars = args.args.evars
    nheapvars = args.args.heapvars
    nprogs = args.args.progs
    pwidth = log2(sz + consts + nargs + 2 - 1)
    pwidth = max(pwidth, 1)
    ewidth = max(width/4, 1)
    mwidth = width - ewidth - 1
    nnondet = args.args.nondet
    maxfit = args.args.maxfit

    self.sz = sz
    self.width = width

    self.verif = verif
    self.scratchfile = tempfile.NamedTemporaryFile(suffix=".c",
        delete=not args.args.keeptemps)

    exedir = os.path.dirname(sys.argv[0])
    interpreter = os.path.join(exedir, args.args.interpreter)
    lib = os.path.join(exedir, args.args.lib)
    explicitdir = os.path.join(exedir, "explicit")
    geneticdir = os.path.join(exedir, "genetic")
    annealdir = os.path.join(exedir, "anneal")
    cbmcdir = os.path.join(exedir, "cbmc")

    genericargs = [
        "-I%s" % interpreter,
        "-I%s" % lib,
        "-DMWIDTH=%d" % mwidth,
        "-DWIDTH=%d" % width,
        "-DNARGS=%d" % nargs,
        "-DNEVARS=%d" % nevars,
        "-DNHEAP=%d" % nheapvars,
        "-DNPROGS=%d" % nprogs,
        "-DCONSTS=%d" % consts,
        "-DPWIDTH=%d" % pwidth,
        "-DNONDET_ARGS=%d" % nnondet,
        "-DMAXFIT=%d" % maxfit,
        os.path.join(interpreter, "exclude.c"),
        os.path.join(interpreter, "wellformed.c"),
        os.path.join(lib, "solution.c"),
        os.path.join(lib, "io.c"),
        self.scratchfile.name] + args.args.checker

    if args.args.float:
      genericargs.insert(0, "-DFLOAT")

    if not args.args.nosymmetry:
      genericargs.insert(0, "-DREMOVE_SYMMETRIC")

    if not args.args.nonops:
      genericargs.insert(0, "-DREMOVE_NOPS")

    if not args.args.noconsts:
      genericargs.insert(0, "-DREMOVE_CONST")

    if args.args.seed is not None:
      genericargs.append("-DSEED=%d" % args.args.seed)

    if verif:
      if args.args.fastverif == True:
        execcfile = "/tmp/exec.c"
      else:
        execcfile = os.path.join(interpreter, "exec.c")

      self.cbmcargs = [args.args.cbmc,
          "-DSZ=%d" % sz,
          execcfile,
          "-DNRES=%d" % sz,
          os.path.join(cbmcdir, "verif.c"), "--32"] + genericargs

      self.gccargs["explicit"] = [args.args.gcc, "-DSEARCH", "-std=c99", "-lm",
          "-DSZ=128",
          "-DNRES=128",
          execcfile,
          #os.path.join(interpreter, "exec.c"),
          "-O0", "-g", os.path.join(explicitdir, "verif.c")] + genericargs
    else:
      self.cbmcargs = [args.args.cbmc, "-DSYNTH",
          "-DSZ=%d" % sz,
          os.path.join(interpreter, "exec.c"),
          os.path.join(cbmcdir, "synth.c")] + genericargs
      self.gccargs["explicit"] = [args.args.gcc, "-DSEARCH", "-std=c99",
          "-DSZ=%d" % sz,
          "-DNRES=%d" % sz,
          os.path.join(interpreter, "exec.c"),
          "-O0", "-g",
          os.path.join(explicitdir, "synth.c"), "-lm"] + genericargs
      self.gccargs["genetic"] = [args.args.gcc,
          "-std=c99",
          "-DSEARCH",
          "-DSZ=128",
          "-DNRES=128",
          "-DPOPSIZE=%d" % args.args.popsize,
          "-DKEEPFRAC=%d" % args.args.keepfrac,
          "-DNEWFRAC=%d" % args.args.newfrac,
          "-DNEWSIZE=%d" % args.args.newsize,
          "-DTOURNEYSIZE=%d" % args.args.tourneysize,
          "-DMUTATION_PROB=%.03f" % args.args.mutprob,
          "-DRECOMBINE_PROB=%.03f" % args.args.recombprob,
          "-DREPLACE_PROB=%.03f" % args.args.replaceprob,
          "-DSAVEFILE=\"%s\"" % geneticsave.name,
          os.path.join(interpreter, "exec.c"),
          "-O0", "-g",
          os.path.join(geneticdir, "synth.c"), "-lm"] + genericargs
      self.gccargs["anneal"] = [args.args.gcc, "-DSEARCH", "-std=c99",
          "-DSZ=%d" % sz,
          "-DNRES=%d" % sz,
          os.path.join(interpreter, "exec.c"),
          "-O0", "-g",
          os.path.join(annealdir, "synth.c"), "-lm"] + genericargs


    if not args.args.noslice:
      self.cbmcargs.append("--slice-formula")

    if args.args.z3:
      self.cbmcargs.append("--z3")


    self.write = self.scratchfile.write

  def run(self):
    self.scratchfile.flush()
    perf.start("checker")
    procs = []
    bins = {}  # 用于存储所有二进制文件路径
    retfile = None

    strategy = None

    if args.args.verif_strategy == "default":
      args.args.verif_strategy = args.args.strategy

    if args.args.synth_strategy == "default":
      args.args.synth_strategy = args.args.strategy

    if self.verif:
      if args.args.verif_strategy in ("all", "evolve"):
        strategies = ["explicit", "cbmc"]
      else:
        strategies = [args.args.verif_strategy]
    else:
      if args.args.synth_strategy == "all":
        strategies = ["explicit", "cbmc", "genetic", "anneal"]
      elif args.args.synth_strategy == "evolve":
        strategies = ["genetic", "anneal"]
      else:
        strategies = [args.args.synth_strategy]

    try:
      if "cbmc" in strategies:
        if args.args.verbose > 1:
          print(" ".join(self.cbmcargs))

        cbmcfile = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps)
        cbmcproc = subprocess.Popen(self.cbmcargs, stdout=cbmcfile,
            preexec_fn=os.setpgrp)
        procs.append((cbmcproc, cbmcfile, "cbmc"))

      for s in ("explicit", "genetic", "anneal"):
        if s in strategies:
          bin_path = self.compile(s)
          bins[s] = bin_path  # 存储二进制文件路径
          outfile = tempfile.NamedTemporaryFile(delete=not args.args.keeptemps)

          if args.args.verbose > 1:
            print(bin_path)

          # 确保文件存在且可执行
          if os.path.exists(bin_path) and os.access(bin_path, os.X_OK):
            proc = subprocess.Popen([bin_path], stdout=outfile,
                preexec_fn=os.setpgrp)
            procs.append((proc, outfile, s))
          else:
            raise OSError(f"Binary file {bin_path} does not exist or is not executable")

      (finished, retcode) = os.wait()
      
      # 找到完成进程的输出文件
      for (proc, outfile, checker) in procs:
        if proc.pid == finished:
          retfile = outfile
          perf.inc(checker)
          if args.args.verbose > 0:
            print(f"Fastest checker: {checker}")
          break

      if retfile is None:
        raise RuntimeError("No checker completed successfully")

      retfile.seek(0)
      return (os.WEXITSTATUS(retcode), retfile)

    finally:
      perf.end("checker")

      # 关闭所有打开的文件，除了返回的文件
      for (proc, outfile, _) in procs:
        try:
          os.killpg(proc.pid, signal.SIGKILL)
          proc.wait()
        except:
          pass
        if outfile != retfile:
          outfile.close()

      # 清理临时文件（如果不需要保留）
      if not args.args.keeptemps:
        for path in bins.values():
          try:
            os.unlink(path)
          except:
            pass

  def cachable(self, param):
    width, key = param
    if args.args.fastverif:
      return key == "genetic-synth"
    else:
      return key in ("genetic-synth", "explicit-verif")

  def compile(self, name):
    global compiled

    if self.verif:
        key = (self.width, name + "-verif")
    else:
        key = (self.width, name + "-synth")

    if not self.cachable(key) or key not in compiled:
        # 创建临时文件，确保使用参数指定的目录
        ofiledir = args.args.ofiledir
        if not os.path.exists(ofiledir):
            try:
                os.makedirs(ofiledir, exist_ok=True)
                if args.args.verbose > 0:
                    print(f"Created directory: {ofiledir}")
            except Exception as e:
                print(f"Warning: Could not create directory {ofiledir}: {str(e)}")
                ofiledir = "/tmp"  # 回退到 /tmp
                
        # 不再尝试修改 /tmp 目录的权限
        # 生成唯一文件名
        path = os.path.join(ofiledir, f"checker_{name}_{os.getpid()}")
        
        gcc = self.gccargs[name] + ["-o", path, "-lm"]
        
        perf.start("gcc")
        try:
            if args.args.verbose > 0:
                print(f"Compiling checker: {name}")
                print(f"Output path: {path}")
                print(f"Command: {' '.join(gcc)}")
            
            # 显示编译输出，便于调试
            process = subprocess.Popen(gcc, 
                                      stdout=subprocess.PIPE, 
                                      stderr=subprocess.PIPE)
            stdout, stderr = process.communicate()
            result = process.returncode
            
            if result != 0:
                print(f"Compilation failed with exit code {result}")
                print(f"Standard output: {stdout.decode('utf-8', errors='replace')}")
                print(f"Standard error: {stderr.decode('utf-8', errors='replace')}")
                raise RuntimeError(f"Compilation failed with exit code {result}")
                
            # 验证文件是否创建成功
            if not os.path.exists(path):
                print(f"Error: Compiled file {path} was not created")
                raise RuntimeError(f"Compiled file {path} was not created")
            
            # 明确设置文件权限 - 只修改新创建的文件，不修改目录
            try:
                os.chmod(path, 0o755)
            except Exception as e:
                print(f"Warning: Could not set permissions on {path}: {str(e)}")
                # 即使无法修改权限，也继续执行，因为文件可能已经可执行
            
            if args.args.verbose > 0:
                print(f"Successfully compiled: {path}")
                print(f"File exists: {os.path.exists(path)}")
                print(f"Executable: {os.access(path, os.X_OK)}")
            
            # 注册清理函数
            if not args.args.keeptemps:
                import atexit
                atexit.register(lambda p=path: os.unlink(p) if os.path.exists(p) else None)
            
            compiled[key] = path
            return path
        except Exception as e:
            # 出错时清理
            print(f"Exception during compilation: {str(e)}")
            try:
                if os.path.exists(path):
                    os.unlink(path)
            except:
                pass
            raise RuntimeError(f"Failed to compile {name} checker: {str(e)}")
        finally:
            perf.end("gcc")
    else:
        # 使用缓存版本时，验证文件仍然存在
        path = compiled[key]
        if not os.path.exists(path) or not os.access(path, os.X_OK):
            # 缓存的文件不存在或不可执行，删除缓存记录
            del compiled[key]
            # 重新编译
            return self.compile(name)
        return path