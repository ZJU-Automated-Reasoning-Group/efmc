# coding: utf8
import os
# import sys
import subprocess
from threading import Timer
from typing import List

# import signal
# import psutil
# import zlib


g_input_type = "sygus"
g_run_efsmt = False
g_run_pdr = False
g_run_kind = True


def find_smt2_files(path: str) -> List[str]:
    files_list = []  # path to smtlib2 files
    # print(path)
    for root, dirs, files in os.walk(path):
        for filename in files:
            tt = os.path.splitext(filename)[1]
            if tt == '.smt2' or tt == '.sl':
                files_list.append(os.path.join(root, filename))
    return files_list


def terminate(process: subprocess.Popen, is_timeout: List[bool]):
    if process.poll() is None:
        try:
            # process.terminate()
            process.kill()  # ?
            is_timeout[0] = True
        except Exception as es:
            # print("error for interrupting")
            print(es)
            pass


def solve_with_bin_solver(cmd: List[str], timeout: int) -> str:
    """ cmd should be a complete cmd"""
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


def solve_file(file_path: str):
    cur_dir = os.path.dirname(os.path.realpath(__file__))
    # cmd = [".../cvc5/build/bin/cvc5", "-q"]
    if g_input_type == "sygus":
        if g_run_efsmt:
            cmd = ["python3", cur_dir + "/prover.py", "--engine", "efsmt", "--lang", "sygus", "--file", file_path]
            out = solve_with_bin_solver(cmd, 5)
            print(out)
        if g_run_pdr:
            cmd2 = ["python3", cur_dir + "/prover.py", "--engine", "pdr", "--lang", "sygus", "--file", file_path]
            out2 = solve_with_bin_solver(cmd2, 5)
            print(out2)
    elif g_input_type == "chc":
        if g_run_efsmt:
            cmd = ["python3", cur_dir + "/prover.py", "--engine", "efsmt",
                   "--template", "bv_interval", "--lang", "chc", "--file", file_path]
            out = solve_with_bin_solver(cmd, 5)
            print(out)
        if g_run_pdr:
            cmd2 = ["python3", cur_dir + "/prover.py", "--engine", "pdr", "--lang", "chc", "--file", file_path]
            # print(cmd)
            out2 = solve_with_bin_solver(cmd2, 5)
            print(out2)
        if g_run_kind:
            cmd3 = ["python3", cur_dir + "/prover.py", "--engine", "kind", "--lang", "chc", "--file", file_path]
            # print(cmd)
            out3 = solve_with_bin_solver(cmd3, 5)
            print(out3)
    else:
        print("Unsupported frontend: ", g_input_type)
        exit(0)


def solve_dir(path: str):
    all_files = find_smt2_files(path)
    # print(all_files)
    for file in all_files:
        print("Solving: ", file)
        solve_file(file)


if __name__ == "__main__":
    g_input_type = "chc"
    current_dir = os.path.dirname(os.path.realpath(__file__))
    if g_input_type == "sygus":
        solve_dir(current_dir + "/benchmarks/chc/bv/2017.ASE_FIB/8bits_signed/")
    elif g_input_type == "chc":
        solve_dir(current_dir + "/benchmarks/chc/bv/2017.ASE_FIB/8bits_signed/")
    else:
        print("Input type not supported!")
        exit(0)
