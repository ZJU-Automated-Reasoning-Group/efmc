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
CEGIS_SMT = "z3"1
END_WITH = "smt2"
MAXTIME = 1
STRENGTHEN = False
CUR_DIR = os.path.dirname(os.path.realpath(__file__))
BENCHMARK_DIR = "/Benchmark"
Processed_PATH = "/SafeBenchmark"
RESULT_DIR = "./Result"
ENDWITH = '.smt2'
pbar_lock  =Lock()
traverse_lang = ['none']
traverse_method = ['none']
traverse_solver = ['none']
traverse_cegis_solver = ['none']

all_lang = ['chc', 'sygus']
all_method = ['kind', 'pdr', 'efsmt']
all_solver = ['z3', 'cvc5', 'btor', 'yices2', 'mathsat', 'bitwuzla']
all_pysmt_solver = ['z3', 'msat', 'yices', 'btor']
all_template = ["bv_interval", "power_bv_interval",
                "bv_zone", "power_bv_zone",
                "bv_octagon", "power_bv_octagon",
                "bv_poly", "power_bv_poly"]
all_sat_solver=['z3sat','cd', 'cd15', 'gc3', 'gc4', 'g3',
                             'g4', 'lgl', 'mcb', 'mpl', 'mg3',
                             'mc', 'm22', 'mgh']  
all_endwith = ['c', 'smt2', 'sl']


#################### By KJY #########################
# def csv_create(method,lang,results_list):
#     header=['file_name','error?','template','constraint','solve or not','invariant','config']
#     first_last_slash_index = GOAL_PATH.rfind('/', 0,)
#     file_name = GOAL_PATH[first_last_slash_index+1:]
#     csv_name=file_name+"_"+method+"_"+lang+".csv"
#     with open(csv_name,'w',newline='') as file:
#         writer=csv.writer(file)
#         writer.writerow(header)
#         writer.writerows(results_list)


def parsing_out(file_path, template, lines, mode='kind'):
    result_dict = {
        'file': file_path[file_path.rfind('/') + 1:],
        'method': mode}
    if template != 'none':
        result_dict['template'] = template
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


def data_process(results):
    file_name = []
    save_safe_dir = CUR_DIR + Processed_PATH
    origin_path = CUR_DIR+BENCHMARK_DIR
    if not os.path.isdir('SafeBenchmark'):
        os.mkdir('SafeBenchmark')
    for result in results:
        if 'safe' not in result or not result['safe']:
            continue
        name = result['file']
        if name in file_name:
            continue
        file_name.append(name)
        relative_path = result['origin_relpath']
        safe_path = os.path.join(save_safe_dir, relative_path)
        if not os.path.exists(os.path.dirname(safe_path)):
            os.makedirs(os.path.dirname(safe_path))
        shutil.copy(
            os.path.join(
                origin_path, relative_path), os.path.join(
                save_safe_dir, relative_path))

#####################################################


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


def solve_file(file_path, ef_template, smt_solver, cegis_solver):
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
        cmd.append("--template")
        cmd.append(ef_template)
    if smt_solver != "none":
        cmd.append("--smt-solver")
        cmd.append(smt_solver)
        # cmd.append("--validate-invariant")
    if cegis_solver != "none":
        cmd.append("--cegis-solver")
        cmd.append(cegis_solver)
    if STRENGTHEN:
        cmd.append("--prop-strengthen")
    if NUM_DISJUNCTIONS:
        cmd.append("--num-disjunctions")
        cmd.append(str(NUM_DISJUNCTIONS))
    out, duration = solve_with_bin_solver(cmd, MAXTIME)
    lines = out.split('\n')
    print(lines)
    return parsing_out(file_path, ef_template, lines, mode=METHOD), duration


def find_safe(root, num_of_thread):
    file_list = []

    if not os.path.isdir(RESULT_DIR):
        os.mkdir(RESULT_DIR)
    # get all .smt2 [chc format]
    for dirpath, _, filenames in os.walk(root):
        for filename in filenames:
            if filename.endswith("." + END_WITH):
                file_path = os.path.join(dirpath, filename)
                file_list.append(file_path)

    if METHOD == 'efsmt':
        templates = all_template
    else:
        templates = ['none']

    def multi_func(files, result_queue):
        result_list = []
        for file in files:
            file_name = os.path.splitext(os.path.basename(file))[0]
            relative_path = os.path.relpath(file, root)
            no_ext_path, _ = os.path.splitext(relative_path)
            new_path = os.path.join(RESULT_DIR, no_ext_path)
            new_path = new_path + "/"
            if not os.path.exists(new_path):
                os.makedirs(new_path)
            for template in templates:
                if NUM_DISJUNCTIONS and "power" not in template:
                    continue
                result, duration_time = solve_file( 
                    file, template, SMT, CEGIS_SMT)
                result['time'] = duration_time
                if CEGIS_SMT == 'none':
                    save_path = new_path + file_name + "_" + METHOD + \
                        "_" + template + "_smt_" + SMT + ".json"
                    result['smt_solver'] = SMT
                else:
                    save_path = new_path + file_name + "_" + METHOD + "_" + \
                        template + "_cegis_smt_" + CEGIS_SMT + ".json"
                    result['cegis_solver'] = CEGIS_SMT
                result['origin_relpath'] = relative_path
                
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
            file_list[start_index:end_index], result_queue))
        process.start()
        processes.append(process)

    for process in processes:
        process.join()

    
    all_results = []
    for _ in range(num_of_thread):
        all_results.extend(result_queue.get())
    data_process(all_results)
    return all_results


def Initial():
    if LANG not in all_lang:
        raise Exception(
            "An error occurred: Unexpected language used in verfication.")
    if METHOD not in all_method:
        raise Exception(
            "An error occurred: Unexpected method used in verfication.")
    if METHOD != 'efsmt':
        if SMT != 'z3' or (CEGIS_SMT != 'z3' and CEGIS_SMT != 'none'):
            return False
    if LANG == 'sygus' and METHOD == 'kind':
        print("do not combine sygus and kind, which is not a valid combination")
        return False
    if SMT != 'cegis' and CEGIS_SMT != 'none':
        return False
    return True


def option_set(args):
    global traverse_lang
    global traverse_method
    global traverse_solver
    global traverse_cegis_solver
    traverse_lang = all_lang
    traverse_method = all_method
    traverse_solver = all_solver
    if args.complete_experiment:
        traverse_cegis_solver = all_pysmt_solver
    pass


def depend_on_Lang(language):
    if language == 'C':
        return 'c'
    if language == 'chc':
        return 'smt2'
    if language == 'sygus':
        return 'sygus'
    if language == 'cpp':
        return 'cpp'
    pass


def count_values(row_data):
    count_T = 0
    count_F = 0
    count_U = 0
    count_X =0
    for _, value in row_data.items():
        if "T" in value:
            count_T += 1
        elif "F" in value:
            count_F += 1
        elif "U" in value:
            count_U += 1
        elif "X" in value:
            count_X+=1
    return count_T, count_F, count_U,count_X


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('-l', '--lang', type=str, nargs='+', default="none")
    parser.add_argument('-m', '--method', type=str, nargs='+', default="none")
    parser.add_argument('-p', '--goal_path', default=BENCHMARK_DIR)
    parser.add_argument('-t', '--time', default=MAXTIME)
    parser.add_argument('-th', '--thread', default=cpu_count())
    parser.add_argument('--prop-strengthen', action='store_true')
    parser.add_argument(
        '-mp',
        '--paint-mode',
        type=str,
        nargs='+',
        default='none')
    parser.add_argument(
        '-s',
        "--smt-solver",
        type=str,
        nargs='+',
        default="none")
    parser.add_argument(
        '-cs',
        "--cegis-smt",
        type=str,
        nargs='+',
        default="none")
    # parser.add_argument(
    #     '--select-safe',
    #     action='store_true',
    #     help='Select all the safe benchmark.')
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
    save_dir = './Result'
    if not os.path.exists(save_dir):
        os.makedirs(save_dir)
    save_dir+='/'
    paint_mode = args.paint_mode
    CEGIS_SMT = args.cegis_smt
    SMT = args.smt_solver
    METHOD = args.method
    LANG = args.lang
    STRENGTHEN = args.prop_strengthen
    MAXTIME = int(args.time)
    NUM_DISJUNCTIONS = args.num_disjunctions

    figure_name = "Experiment"
    if NUM_DISJUNCTIONS:
        figure_name += "_dis_" + str(NUM_DISJUNCTIONS)
    if STRENGTHEN:
        figure_name += "_strengthen"
    if MAXTIME:
        figure_name += "_maxtime_" + str(MAXTIME)

    print("Used Thread Number", cpu_count())
    option_set(args)
    # select the benchmark with safe property

    BENCHMARK_DIR = args.goal_path
    
    total_iterations = (
        len(traverse_lang) *
        len(traverse_method) *
        len(traverse_solver) *
        len(traverse_cegis_solver)
    )
    count=0

    for Language, Method, Solver, Ceg_Solver in itertools.product(
            traverse_lang, traverse_method, traverse_solver, traverse_cegis_solver):
        LANG = Language
        if LANG == 'sygus':
            continue
        END_WITH = depend_on_Lang(LANG)
        METHOD = Method
        SMT = Solver
        CEGIS_SMT = Ceg_Solver
        run = Initial()
        print("---------------------------------------")
        print(f"The process of total task is:{count}/{total_iterations}")
        count+=1
        if run:
            data_list=find_safe(CUR_DIR + BENCHMARK_DIR, int(args.thread))
        print("---------------------------------------")
    safe_file = []
    for data in data_list:
        if 'safe' in data and data['safe']:
            safe_file.append(data['file'])
    safe_file = list(set(safe_file))

    #mode=1 -> output csv to learn the result of the efmc
    if "1" in paint_mode:
        row_names = set()
        for data in data_list:
            row_names.add(
                (data['smt_solver'],
                 data['method'],
                    data.get(
                    'template',
                    '_notemp')))
        row_names = sorted(list(row_names))

        table = {row_name: {file: "" for file in safe_file}
                 for row_name in row_names}

        for data in data_list:
            if data['file'] in safe_file:
                row_name = (
                    data['smt_solver'],
                    data['method'],
                    data.get(
                        'template',
                        '_notemp'))
                if data.get('timeout'):
                    value="X"
                elif data.get('safe', -1) != -1:
                    if data['safe']:
                        value = "T"
                    else:
                        value = "F"
                elif data.get('unknown', -1) != -1:
                    if data['unknown']:
                        value = "U"
                    else:
                        raise Exception(
                            "An error occurred: Unknown has False value.")
                else:
                    value = "Err"
                table[row_name][data['file']] = value
        with open(save_dir+figure_name + ".csv", "w", newline="", encoding="utf-8") as csvfile:
            writer = csv.writer(csvfile)
            # 写入标题行
            writer.writerow([""] + safe_file + ["T", "F", "U","X"])
            # 写入数据行
            for row_name in row_names:
                row_data = table[row_name]
                count_T, count_F, count_U ,count_X= count_values(row_data)
                row = [f"{row_name[0]}_{row_name[1]}_{row_name[2]}"] + [row_data[file]
                                                                        for file in safe_file] + [count_T, count_F, count_U,count_X]
                writer.writerow(row)
    #mode=2 -> output the figure about the max solving rate of efsmt,pdr,kind.
    if "2" in paint_mode:
        time_data = {}
        count_data = {}
        for data in data_list:
            if data['file'] not in safe_file:
                continue

            if 'template' not in data:
                key = (data['smt_solver'], data['method'])
            else:
                key = (data['smt_solver'], data['method'], data['template'])

            if key not in time_data:
                time_data[key] = [0] * len(safe_file)
                count_data[key] = [0] * len(safe_file)
            time_data[key][safe_file.index(data['file'])] += data['time']
            count_data[key][safe_file.index(
                data['file'])] += data.get('safe', 0)

        cumulative_time_data = {}
        cumulative_count_data = {}
        for key, values in time_data.items():
            cumulative_time_data[key] = [
                sum(values[:i + 1]) for i in range(len(values))]
        for key, values in count_data.items():
            cumulative_count_data[key] = [
                sum(values[:i + 1]) for i in range(len(values))]

        efsmt_data = {
            k: v for k,
            v in cumulative_count_data.items() if k[1] == 'efsmt'}
        non_efsmt_data = {
            k: v for k,
            v in cumulative_time_data.items() if k[1] != 'efsmt'}

        for key, count in count_data.items():
            count_data[key] = list(itertools.accumulate(count))

        efsmt_verification_rates = {
            key: count_data[key][-1] / len(safe_file)
            for key in efsmt_data.keys()
        }

        max_verification_rate = max(efsmt_verification_rates.values())
        top_verification_rate_efsmt = [
            key
            for key, rate in efsmt_verification_rates.items()
            if rate == max_verification_rate
        ]

        plot_data = {key: efsmt_data[key]
                     for key in top_verification_rate_efsmt}
        plot_data.update(non_efsmt_data)
        markers = ["o", "v", "^", "<", ">", "s", "p", "*", "X",
                   "D", "h", "H", "+", "x", "1", "2", "3", "4", "|", "_"]
        marker_cycle = itertools.cycle(markers)
        sns.set(style="darkgrid")
        plt.figure(figsize=(12, 6))
        for key, values in plot_data.items():
            if len(key) == 3:
                label = f"{key[0]}_{key[1]}_{key[2]}"
            else:
                label = f"{key[0]}_{key[1]}"
            sns.lineplot(
                x=range(1, len(safe_file) + 1),
                y=cumulative_time_data[key],
                label=label,
                marker=next(marker_cycle),
            )
        plt.xticks(range(1, len(safe_file) + 1), [""] * len(safe_file))
        plt.xlabel("File Index")
        plt.ylabel("Cumulative Time")
        plt.title("Cumulative Time vs. File Index")
        plt.legend()
        plt.savefig(save_dir+figure_name + ".png", dpi=300)

        print("Efsmt methods with the highest cumulative verification rate:")
        for key in top_verification_rate_efsmt:
            verification_rate = count_data[key][-1] / len(safe_file) * 100
            if len(key) == 3:
                label = f"{key[0]}_{key[1]}_{key[2]}"
            else:
                label = f"{key[0]}_{key[1]}"
            print(f"{label}: {verification_rate:.2f}%")

        print("Cumulative verification rate for non-efsmt methods:")
        for key in non_efsmt_data.keys():
            verification_rate = count_data[key][-1] / len(safe_file) * 100
            if len(key) == 3:
                label = f"{key[0]}_{key[1]}_{key[2]}"
            else:
                label = f"{key[0]}_{key[1]}"
            print(f"{label}: {verification_rate:.2f}%")

    #mode=3 -> RQ1 : Compare the difference template while fix smt_solver.
    if "3" in paint_mode:
        efsmt_data = [
            data for data in data_list if data["method"] == "efsmt" and data["file"] in safe_file
        ]

        cumulative_time_data = {}
        for data in efsmt_data:
            key = (data["smt_solver"], data["template"])
            if key not in cumulative_time_data:
                cumulative_time_data[key] = [0] * len(safe_file)
            file_idx = safe_file.index(data["file"])
            cumulative_time_data[key][file_idx] = data["time"]

        for key, time_list in cumulative_time_data.items():
            cumulative_time_data[key] = list(itertools.accumulate(time_list))

        smt_solvers = sorted(list(set([data["smt_solver"] for data in efsmt_data])))
        for smt_solver in smt_solvers:
            plt.figure(figsize=(12, 6))
            plt.title(f"SMT Solver: {smt_solver}")

            plot_data = {
                key: cumulative_time_data[key]
                for key in cumulative_time_data.keys()
                if key[0] == smt_solver
            }
            marker_cycle = itertools.cycle(("o", "v", "s", "p", "*", "h", "H", "+", "x", "D", "|", "_"))

            for key, values in plot_data.items():
                label = f"{key[0]}_{key[1]}"
                sns.lineplot(
                    x=range(1, len(safe_file) + 1),
                    y=cumulative_time_data[key],
                    label=label,
                    marker=next(marker_cycle),
                )

            plt.xlabel("File Index")
            plt.ylabel("Cumulative Time (s)")
            plt.legend()
            plt.savefig(save_dir+figure_name+"_smt_"+smt_solver+"_template_comp.png",dpi=300)
    
    if "4" in paint_mode:
        efsmt_data = [
            data for data in data_list if data["method"] == "efsmt" and data["file"] in safe_file
        ]

        cumulative_time_data = {}
        for data in efsmt_data:
            key = (data["smt_solver"], data["template"])
            if key not in cumulative_time_data:
                cumulative_time_data[key] = [0] * len(safe_file)
            file_idx = safe_file.index(data["file"])
            cumulative_time_data[key][file_idx] = data["time"]

        for key, time_list in cumulative_time_data.items():
            cumulative_time_data[key] = list(itertools.accumulate(time_list))

        templates = sorted(list(set([data["template"] for data in efsmt_data])))
        for template in templates:
            plt.figure(figsize=(12, 6))
            plt.title(f"Template: {template}")

            plot_data = {
                key: cumulative_time_data[key]
                for key in cumulative_time_data.keys()
                if key[1] == template
            }
            marker_cycle = itertools.cycle(("o", "v", "s", "p", "*", "h", "H", "+", "x", "D", "|", "_"))

            for key, values in plot_data.items():
                label = f"{key[0]}_{key[1]}"
                sns.lineplot(
                    x=range(1, len(safe_file) + 1),
                    y=cumulative_time_data[key],
                    label=label,
                    marker=next(marker_cycle),
                )

            plt.xlabel("File Index")
            plt.ylabel("Cumulative Time (s)")
            plt.legend()
            plt.savefig(save_dir+figure_name+"_template_"+template+"_smt_comp.png", dpi=300)
            