# coding: utf8
import os
import subprocess
from threading import Timer

# import zlib

"""
Run benchmarks
"""


def find_smt2_files(path):
    flist = []  # path to smtlib2 files
    for root, dirs, files in os.walk(path):
        for fname in files:
            tt = os.path.splitext(fname)[1]
            if tt == '.smt2' or tt == '.sl':
                flist.append(os.path.join(root, fname))
    return flist


def terminate(process, is_timeout):
    if process.poll() is None:
        try:
            process.terminate()
            # process.kill()
            is_timeout[0] = True
        except Exception as es:
            # print("error for interrupting")
            print(es)
            pass


def solve_with_bin_solver(cmd, timeout=5):
    """
    cmd should be a complete cmd
    """
    # ret = "unknown"
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    is_timeout = [False]
    timer = Timer(timeout, terminate, args=[p, is_timeout])
    timer.start()
    out = p.stdout.readlines()
    out = ' '.join([str(element.decode('UTF-8')) for element in out])
    p.stdout.close()
    timer.cancel()
    if is_timeout[0]:
        return out
        # return "timeout"
    return out


def solve_dir(path):
    # cmd = ["/Users/prism/Work/cvc5/build/bin/cvc5", "-q"]
    cmd = ["python3", "/Users/prism/Work/logicbox/independent/efsmt/prover.py", "--prover", "efsmt", "--file"]
    cmd2 = ["python3", "/Users/prism/Work/logicbox/independent/efsmt/prover.py", "--prover", "pdr", "--file"]
    files = find_smt2_files(path)
    # results = {}
    # print(len(files))
    efsmt_success = 0
    pdr_success = 0
    for file in files:
        print("Solving: ", file)

        cmd.append(file)
        out = solve_with_bin_solver(cmd, 5)
        if "EFSMT success" in out:
            efsmt_success += 1
        print(out)
        cmd.pop()

        cmd2.append(file)
        out2 = solve_with_bin_solver(cmd2, 5)
        if "PDR success" in out2:
            pdr_success += 1
        print(out2)
        cmd2.pop()


solve_dir("/Users/prism/Work/logicbox/independent/efsmt/benchmarks/sygus-inv/LIA/2017.ASE_FiB")
# solve_dir("./benchmarks/sygus-inv/LIA/2018.SV-Comp")
# solve_dir("/Users/prism/Work/logicbox/independent/efsmt/benchmarks/sygus-inv/LIA/2018.NeurIPS_Code2Inv")
# solve_dir("./benchmarks/sygus-inv/LIA/2016.SyGuS-Comp")
# solve_dir("./benchmarks/sygus-inv/LIA/2015.FMCAD_Acceleration")
