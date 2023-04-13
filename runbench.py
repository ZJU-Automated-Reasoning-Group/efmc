# coding: utf8
import os
# import sys
import subprocess
from threading import Timer
from typing import List
import csv
# import signal``
# import psutil
# import zlib


g_input_type = "chc"
all_template=["bv_interval", "power_bv_interval",
                  "bv_zone", "power_bv_zone",
                  "bv_octagon", "power_bv_octagon",
                  "bv_poly", "power_bv_poly"]
g_run_efsmt,g_run_pdr,g_run_kind= True,False,False
No_constraint_output=True
MAXTIME=10
GOAL_PATH="/benchmarks/chc/bv/2017.ASE_FIB/32bits_unsigned"

#################### By KJY #########################
def csv_create(method,lang,results_list):
    header=['file_name','error?','template','constraint','solve or not','invariant','config']
    first_last_slash_index = GOAL_PATH.rfind('/', 0,)  
    file_name = GOAL_PATH[first_last_slash_index+1:]
    csv_name=file_name+"_"+method+"_"+lang+".csv"
    with open(csv_name,'w',newline='') as file:
        writer=csv.writer(file)
        writer.writerow(header)
        writer.writerows(results_list)

def parsing_kind_output(file_path,lines):
    second_last_slash_index = file_path.rfind('/', 0, file_path.rfind('/'))  
    file_path = file_path[second_last_slash_index+1:]
    CHC_read = False
    kind_success = False
    time = 0.0
    kind_solve = True
    config=""
    template="no_template"
    invariant=""
    error=''
    for line in lines:
        if "Finish parsing CHC file" in line:
            CHC_read = True
            continue

        if "K-induction starts" in line:
            kind_success = True
        
        if "time:" in line:
            time = float(line.split()[-1])
            config+='time:'+str(time)+'\n'
            
        if "unknown" in line:
            config+="program safety:unknown"
            break
        
        if "unsafe" in line:
            config+="program safety:unsafe"
            break
        
        if "safe" in line:
            config+="program safety:safe"
            break
    if not CHC_read or not kind_success:
        error="out of maxtime"+str(MAXTIME)+"s"
    if error:
        template='no_template'
        output_str=''
        kind_solve=False
        invariant=''
    if No_constraint_output:
        output_str=""
    result=[file_path,error,template,output_str,kind_solve,invariant,config]
    print(result)
    return result

def parsing_pdr_output(file_path,lines):
    second_last_slash_index = file_path.rfind('/', 0, file_path.rfind('/'))  
    file_path = file_path[second_last_slash_index+1:]
    CHC_read = False
    PDR_success = False
    time = 0.0
    pdr_solve = True
    config=""
    template="no_template"
    invariant=""
    error=''
    for line in lines:
        if "Finish parsing CHC file" in line:
            CHC_read = True
            continue

        if "PDR starting!!!" in line:
            PDR_success = True
        
        if "time:" in line:
            time = float(line.split()[-1])
            config+='time:'+str(time)+'\n'
            
        if "PDR error" in line:
            error="unexpected error occur in pdr"
            pdr_solve=False
        
        if "unsafe" in line:
            config+="program safety:unsafe"
            break
        elif "safe" in line:
            config+="program safety:safe"
            break
    if error:
        error=error
    elif not CHC_read or not PDR_success:
        error="out of maxtime"+str(MAXTIME)+"s"
    if error:
        template='no_template'
        output_str=''
        pdr_solve=False
        invariant=''
    if No_constraint_output:
        output_str=""
    result=[file_path,error,template,output_str,pdr_solve,invariant,config]
    return result

def parsing_efsmt_output(file_path,template,lines):       
    second_last_slash_index = file_path.rfind('/', 0, file_path.rfind('/'))  
    file_path = file_path[second_last_slash_index+1:]
    CHC_read = False
    overflow = False
    over_flow_read = False
    underflow = False
    solving = False
    constraint=False
    output_str = ""
    NO_BV=False
    EFSMT_success = False
    fail_time = 0.0
    template_solve = True
    config=""
    invariant=""
    for line in lines:
        if "Finish parsing CHC file" in line:
            CHC_read = True
            continue
        
        if "prevent over/under flow" in line:
            words = line.split()
            overflow = eval(words[-2])
            underflow = eval(words[-1])
            config+='overflow:'+str(overflow)+'\n'
            config+='underflow:'+str(underflow)+'\n'

        if "Start solving: " in line:
            solving = True
        
        if "Used template:" in line:
            template = line.split(":")[-1].strip()
            
        if "EFSMT starting!!!" in line:
            EFSMT_success = True
            constraint=False
        
        if "EFSMT fail time:" in line:
            fail_time = float(line.split()[-1])
            
        if "Cannot verify using the template!" in line:
            template_solve = False
        
        if constraint:
            output_str += line
            output_str+='\n'
        
        if "Used logic:" in line:
            logic = line.split(":")[-1].strip()
            if "BV" not in logic:
                NO_BV=True
            constraint=True
            config+='Not_BV?:'+str(NO_BV)+'\n'
    error=''
    if not CHC_read or not EFSMT_success:
        error="out of maxtime"+str(MAXTIME)+"s"
    if error:
        output_str=''
        template_solve=False
        invariant=''
    if No_constraint_output:
        output_str=""
    result=[file_path,error,template,output_str,template_solve,invariant,config]
    return result
#####################################################

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
    # for i in out:
    #     print(str(i))
    out = ' '.join([str(element.decode('UTF-8')) for element in out])
    p.stdout.close()
    timer.cancel()
    if is_timeout[0]:
        return out
        # return "timeout"
    return out


def solve_file(file_path: str,template):
    cur_dir = os.path.dirname(os.path.realpath(__file__))
    if g_input_type == "sygus":
        if g_run_efsmt:
            cmd = ["python3", cur_dir + "/prover.py", "--engine", "efsmt", "--lang", "sygus", "--file", file_path]
            out = solve_with_bin_solver(cmd, MAXTIME)
        if g_run_pdr:
            cmd = ["python3", cur_dir + "/prover.py", "--engine", "pdr", "--lang", "sygus", "--file", file_path]
            out = solve_with_bin_solver(cmd, MAXTIME)
    elif g_input_type == "chc":
        if g_run_efsmt:
            cmd = ["python3", cur_dir + "/prover.py", "--engine", "efsmt",
                   "--template", str(template), "--lang", "chc", "--file", file_path]
            out = solve_with_bin_solver(cmd, MAXTIME)
        if g_run_pdr:
            cmd = ["python3", cur_dir + "/prover.py", "--engine", "pdr", "--lang", "chc", "--file", file_path]
            # print(cmd)
            out = solve_with_bin_solver(cmd, MAXTIME)
        if g_run_kind:
            cmd = ["python3", cur_dir + "/prover.py", "--engine", "kind", "--lang", "chc", "--file", file_path]
            # print(cmd)
            out = solve_with_bin_solver(cmd, MAXTIME)
    else:
        print("Unsupported frontend: ", g_input_type)
        exit(0)
    lines = out.split('\n')
    print(lines)
    if g_run_efsmt:
        return parsing_efsmt_output(file_path,template,lines)
    if g_run_pdr:
        return parsing_pdr_output(file_path,lines)
    if g_run_kind:
        return parsing_kind_output(file_path,lines)

def solve_dir(path: str):
    all_files = find_smt2_files(path)
    # for file in all_files:
    #     print(file)
    if g_run_efsmt:
        method="efsmt"
    elif g_run_pdr:
        method="pdr"
    else:
        method="kind"
    result=[]
    for file in all_files:
        if method=="efsmt":
            for template in all_template:
                print("Solving: ", file)
                result.append(solve_file(file,template))
        else:
            print("Solving: ", file)
            result.append(solve_file(file,""))
    csv_create(method,g_input_type,result)


if __name__ == "__main__":
    current_dir = os.path.dirname(os.path.realpath(__file__))
    if g_input_type == "sygus":
        solve_dir(current_dir + GOAL_PATH)
    elif g_input_type == "chc":
        solve_dir(current_dir + GOAL_PATH)
    else:
        print("Input type not supported!")
        exit(0)
    
