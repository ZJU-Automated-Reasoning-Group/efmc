# coding: utf8
import os
import subprocess
import glob
from threading import Timer
import time
from typing import List
import csv
from tqdm import tqdm
import shutil
import json
import itertools

import signal
from multiprocessing import Process, cpu_count, Queue,Manager,Lock

import seaborn as sns
import matplotlib.pyplot as plt
NUM_DISJUNCTIONS = 0
LANG = "chc"
METHOD = "efsmt"
SMT = "z3"
CEGIS_SMT = "z3"
END_WITH = "smt2"
TEMPLATE="none"
MAXTIME = 1
STRENGTHEN = False
CUR_DIR = os.path.dirname(os.path.realpath(__file__))
BENCHMARK_DIR = "/Benchmark"
RESULT_DIR = "/Result"
ENDWITH = '.smt2'
pbar_lock  =Lock()
traverse_template = ['none']
traverse_method = ['none']
traverse_solver = ['none']
traverse_cegis_solver = ['none']

all_method = ['kind', 'pdr', 'efsmt']
all_solver = ['z3', 'cvc5', 'btor', 'yices2', 'mathsat', 'bitwuzla']
all_bit_blasting_solver=['z3qbf','caqe','q3b']
all_cegis_solver = ['z3', 'msat', 'yices', 'btor']
all_template = ["bv_interval", "power_bv_interval",
                "bv_zone", "power_bv_zone",
                "bv_octagon", "power_bv_octagon",
                "bv_poly", "power_bv_poly"]
#'cd','gc3','g3','mcb','m22', 'mgh','mpl', 'mg3',
all_sat_solver=['cd15',  'gc4', 'g4', 'lgl',  
                             'mc', ]
all_endwith = ['smt2', 'sl']


def parsing_out(file_path, template, lines, mode='kind'):
    result_dict = {
        'file': file_path[file_path.rfind('/') + 1:],
        'method': mode}

    CHC_read = False
    Method_start = False
    TimeOut = False
    overflow = False
    underflow = False
    # exec_time = -1
    # config = ""
    safe = False
    unknown = False
    error = False
    for line in lines:
        if "Finish parsing CHC file" in line:
            CHC_read = True
            continue

        if "K-induction starts" in line or "PDR starting!!!" in line or "Start solving" in line:
            Method_start = True
            continue

        # if "time:" in line:
        #     exec_time = float(line.split()[-1])
        #     continue

        if "Timeout" in line:
            exec_time = MAXTIME
            TimeOut = True
            break

        if "unknown" in line or "Cannot verify using the template!" in line:
            unknown = True
            continue

        if "unsafe" in line:
            safe = False
            continue
        elif "safe" in line:
            safe = True
            continue
        # pdr specific
        if "PDR error" in line or "Traceback (most recent call last)" in line:
            error = True
            break

        # efsmt specific
        if "prevent over/under flow" in line:
            words = line.split()
            overflow = eval(words[-2])
            underflow = eval(words[-1])
    # result_dict['time']=exec_time
    if TimeOut:
        result_dict['timeout'] = True
        result_dict['unknown'] = True
        return result_dict

    if error or not Method_start or not CHC_read:
        result_dict['unexpected_error'] = True
        return result_dict

    if METHOD == 'efsmt':
        result_dict['overflow'] = overflow
        result_dict['underflow'] = underflow

    if unknown:
        result_dict['unknown'] = unknown
    else:
        result_dict['safe'] = safe

    return result_dict


# def data_process(results):
#     file_name = []
#     save_safe_dir = CUR_DIR + Processed_PATH
#     origin_path = CUR_DIR+BENCHMARK_DIR
#     if not os.path.isdir('SafeBenchmark'):
#         os.mkdir('SafeBenchmark')
#     for result in results:
#         if 'safe' not in result or not result['safe']:
#             continue
#         name = result['file']
#         if name in file_name:
#             continue
#         file_name.append(name)
#         relative_path = result['origin_relpath']
#         safe_path = os.path.join(save_safe_dir, relative_path)
#         if not os.path.exists(os.path.dirname(safe_path)):
#             os.makedirs(os.path.dirname(safe_path))
#         shutil.copy(
#             os.path.join(
#                 origin_path, relative_path), os.path.join(
#                 save_safe_dir, relative_path))

def terminate(process: subprocess.Popen, is_timeout: List[bool]):
    if process.poll() is None:
        try:
            # process.terminate()
            os.kill(process.pid, signal.SIGKILL)
            is_timeout[0] = True
        except Exception as es:
            # print("error for interrupting")
            print(es)
            pass


def solve_with_bin_solver(cmd: List[str], timeout: int) -> str:
    """ cmd should be a complete cmd"""
    # ret = "unknown"
    is_timeout = [False]

    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    timer = Timer(timeout, terminate, args=[p, is_timeout])
    start_time = time.time()
    timer.start()
    out = p.stdout.readlines()
    if is_timeout[0]:
        out.append(
            str.encode(f"Timeout: Method '{METHOD}' timed out after {timeout} seconds.\n"))
    timer.cancel()
    end_time = time.time()
    # for i in out:
    #     print(str(i))
    out = ' '.join([str(element.decode('UTF-8')) for element in out])
    p.stdout.close()
    if is_timeout[0]:
        return out, timeout
        # return "timeout"
    return out, end_time - start_time


def solve_file(file_path, ef_template, smt_solver, cegis_solver,file_name,result):
    cmd = [
        "python3",
        CUR_DIR +
        "/prover.py",
        "--engine",
        METHOD,
        "--lang",
        LANG,
        "--file",
        file_path
    ]
    if ef_template != "none":
        file_name+="_template_"+ef_template
        result['template']=ef_template
        cmd.append("--template")
        cmd.append(ef_template)
    if smt_solver != "none":
        file_name+="_smt_solver_"+smt_solver
        result['smt_solver']=smt_solver
        cmd.append("--smt-solver")
        cmd.append(smt_solver)
        # cmd.append("--validate-invariant")
    if cegis_solver != "none":
        file_name+="_cegis_solver_"+cegis_solver
        result['cegis_solver']=cegis_solver
        cmd.append("--cegis-solver")
        cmd.append(cegis_solver)
    if STRENGTHEN:
        file_name+="_strengthen_"+STRENGTHEN
        result['strengthen']=STRENGTHEN
        cmd.append("--prop-strengthen")
    if NUM_DISJUNCTIONS:
        file_name+="_disjunctions_"+NUM_DISJUNCTIONS
        result['num_disjunctions']=NUM_DISJUNCTIONS
        cmd.append("--num-disjunctions")
        cmd.append(str(NUM_DISJUNCTIONS))
    out, duration = solve_with_bin_solver(cmd, MAXTIME)
    lines = out.split('\n')
    print(lines)
    return parsing_out(file_path, ef_template, lines, mode=METHOD), duration,file_name,result


def find_safe(root, num_of_thread):
    file_list = []

    if not os.path.exists(CUR_DIR+ RESULT_DIR):
        os.makedirs(CUR_DIR+ RESULT_DIR)
    # get all .smt2 [chc format]
    for dirpath, _, filenames in os.walk(root):
        for filename in filenames:
            if filename.endswith("." + END_WITH):
                file_path = os.path.join(dirpath, filename)
                file_list.append(file_path)

    def multi_func(files, result_queue,ef_template):
        result_list = []
        for file in files:
            file_name = os.path.splitext(os.path.basename(file))[0]
            relative_path = os.path.relpath(file, root)
            no_ext_path, _ = os.path.splitext(relative_path)
            new_path = os.path.join(CUR_DIR+RESULT_DIR, no_ext_path)
            new_path = new_path + "/"
            if not os.path.exists(new_path):
                os.makedirs(new_path)
            if NUM_DISJUNCTIONS and "power" not in ef_template:
                continue
            result, duration_time,file_name,result = solve_file( 
                file, ef_template, SMT, CEGIS_SMT,file_name,result)
            result['time'] = duration_time
            save_path = new_path + file_name+".json"
            with open(save_path, 'w') as f:
                json.dump(result, f, indent=4)
            result_list.append(result)
        result_queue.put(result_list)

    num_of_file = len(file_list) // num_of_thread
    remainder = len(file_list) % num_of_thread
    processes = []
    result_queue = Queue()
    
    processes = []
    
    for i in range(num_of_thread):
        start_index = i * num_of_file + min(i, remainder)
        end_index = (i + 1) * num_of_file + min(i + 1, remainder)
        process = Process(target=multi_func, args=(
            file_list[start_index:end_index], result_queue,TEMPLATE))
        process.start()
        processes.append(process)

    for process in processes:
        process.join()

    
    # all_results = []
    # for _ in range(num_of_thread):
    #     all_results.extend(result_queue.get())
    # data_process(all_results)
    return


def depend_on_Method():
    global LANG
    if METHOD in ['efsmt','pdr','eld']:
        LANG='chc'
    else:
        LANG='sygus'
    
def depend_on_Lang():
    global LANG
    if LANG == 'chc':
        return 'smt2'
    if LANG == 'sygus':
        return 'sygus'
    pass




if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('-l', '--lang', type=str, nargs='+', default="none")
    parser.add_argument('-m', '--method', type=str, nargs='+', default="none")
    parser.add_argument('-p', '--goal-path', default=BENCHMARK_DIR)
    parser.add_argument('-t', '--time', default=MAXTIME)
    parser.add_argument('-th', '--thread', default=cpu_count())
    parser.add_argument('--prop-strengthen', action='store_true')
    parser.add_argument(
        '--complete-experiment',
        default=False,
        help='Execute all the comparation and output the corresponding results.')
    parser.add_argument(
        '-d',
        '--num-disjunctions',
        type=int,
        default=0
    )
    args = parser.parse_args()
    save_dir = CUR_DIR+ '/Result'
    if not os.path.exists(save_dir):
        os.makedirs(save_dir)
    save_dir+='/'
    SMT = args.smt_solver
    METHOD = args.method
    LANG = args.lang
    STRENGTHEN = args.prop_strengthen
    MAXTIME = int(args.time)
    NUM_DISJUNCTIONS = args.num_disjunctions

    print("Used Thread Number", cpu_count())
    # select the benchmark with safe property

    BENCHMARK_DIR = args.goal_path
    count=0
    print("---------------------------------------")
    print("---------------------------------------")
    print("-------All Template in efsmt---------")
    traverse_method=['efsmt']
    traverse_solver=all_solver+all_bit_blasting_solver+all_sat_solver
    traverse_cegis_solver=['none']
    traverse_template=all_template
    for Method, Solver, Ceg_Solver,Template in itertools.product(
            traverse_method, traverse_solver, traverse_cegis_solver,traverse_template):
        METHOD = Method
        SMT = Solver
        LANG= depend_on_Method()
        END_WITH = depend_on_Lang()
        CEGIS_SMT = Ceg_Solver
        TEMPLATE=Template
        find_safe(CUR_DIR + BENCHMARK_DIR, int(args.thread))
    print("---------------Finish------------------")
    print("---------------------------------------")
    print("---------------------------------------")
    
    print("---------------------------------------")
    print("---------------------------------------")
    print("-------Cegis Solver in efsmt---------")
    traverse_method=['efsmt']
    traverse_solver=['cegis']
    traverse_cegis_solver=all_cegis_solver
    traverse_template=all_template
    for Method, Solver, Ceg_Solver,Template in itertools.product(
            traverse_method, traverse_solver, traverse_cegis_solver,traverse_template):
        METHOD = Method
        SMT = Solver
        LANG= depend_on_Method()
        END_WITH = depend_on_Lang()
        CEGIS_SMT = Ceg_Solver
        TEMPLATE=Template
        find_safe(CUR_DIR + BENCHMARK_DIR, int(args.thread))
    print("---------------Finish------------------")
    print("---------------------------------------")
    print("---------------------------------------")
    
    print("---------------------------------------")
    print("---------------------------------------")
    print("-------Other Engine in efsmt---------")
    traverse_method=['pdr','eld','cvc5sy']
    traverse_solver=['none']
    traverse_cegis_solver=['none']
    traverse_template=['none']
    for Method, Solver, Ceg_Solver,Template in itertools.product(
            traverse_method, traverse_solver, traverse_cegis_solver,traverse_template):
        METHOD = Method
        SMT = Solver
        LANG= depend_on_Method()
        END_WITH = depend_on_Lang()
        CEGIS_SMT = Ceg_Solver
        TEMPLATE=Template
        find_safe(CUR_DIR + BENCHMARK_DIR, int(args.thread))
    print("---------------Finish------------------")
    print("---------------------------------------")
    print("---------------------------------------")
    