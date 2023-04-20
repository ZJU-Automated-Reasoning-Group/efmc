# coding: utf8
import os
import subprocess
from threading import Timer
from typing import List
import csv
import shutil
import json
import itertools
import signal
from multiprocessing import Process,cpu_count,Queue



LANG=["chc"]
METHOD=["efsmt"]
CUR_DIR = os.path.dirname(os.path.realpath(__file__))
all_template=["bv_interval", "power_bv_interval",
              "bv_zone", "power_bv_zone",
              "bv_octagon", "power_bv_octagon",
              "bv_poly", "power_bv_poly"]

MAXTIME=1
GOAL_PATH="/Benchmark"
Processed_PATH="/SafeBenchmark"
ENDWITH='.smt2'

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

def parsing_out(file_path,template,lines,mode='kind'):
    result_dict={'template':template,'file':file_path[file_path.rfind('/')+1:],'method':mode}
    
    CHC_read=False
    Method_start=False
    TimeOut=False
    overflow=False
    underflow=False
    exec_time = -1
    config=""
    safe=False
    unknown=False
    error=False
    for line in lines:
        if "Finish parsing CHC file" in line:
            CHC_read=True
            continue

        if "K-induction starts" in line or "PDR starting!!!" in line or "Start solving" in line:
            Method_start=True
            continue
        
        if "time:" in line:
            exec_time = float(line.split()[-1])
            continue
        
        if "Timeout" in line:
            exec_time=MAXTIME
            TimeOut=True
            break
            
        if "unknown" in line or "Cannot verify using the template!" in line:
            unknown=True
            continue
        
        if "unsafe" in line:
            safe=False
            continue
        elif "safe" in line:
            safe=True
            continue
        # pdr specific
        if "PDR error" in line:
            error=True
            break

        # efsmt specific
        if "prevent over/under flow" in line:
            words = line.split()
            overflow = eval(words[-2])
            underflow = eval(words[-1])
    result_dict['time']=exec_time
    if TimeOut:
        result_dict['timeout']=True
        result_dict['unknown']=True
        return result_dict
    
    if error or not Method_start or not CHC_read:
        result_dict['unexpected_error']=True
        return result_dict
    
    if METHOD=='efsmt':
        result_dict['overflow']=overflow
        result_dict['underflow']=underflow
    
    if unknown:
        result_dict['unknown']=unknown
    else:
        result_dict['safe']=safe
    
    return result_dict

def data_process(results):
    file_name=[]
    save_safe_dir=CUR_DIR+Processed_PATH
    origin_path=CUR_DIR+GOAL_PATH
    if not os.path.isdir('SafeBenchmark'):
        os.mkdir('SafeBenchmark')
    for result in results:
        if 'safe' not in result or not result['safe']==True:
            continue
        name=result['file']
        if name in file_name:
            continue
        file_name.append(name)
        relative_path=result['origin_relpath']
        safe_path= os.path.join(save_safe_dir, relative_path)
        if not os.path.exists(os.path.dirname(safe_path)):
            os.makedirs(os.path.dirname(safe_path))
        shutil.copy(os.path.join(origin_path, relative_path),os.path.join(save_safe_dir, relative_path))

#####################################################




def terminate(process: subprocess.Popen, is_timeout: List[bool]):
    if process.poll() is None:
        try:
            # process.terminate()
            os.kill(process.pid,signal.SIGKILL)
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
    out= p.stdout.readlines()
    if is_timeout[0]:
        out.append(str.encode(f"Timeout: Method '{METHOD}' timed out after {timeout} seconds.\n"))
    timer.cancel()
    # for i in out:
    #     print(str(i))
    out = ' '.join([str(element.decode('UTF-8')) for element in out])
    p.stdout.close()
    timer.cancel()
    if is_timeout[0]:
        return out
        # return "timeout"
    return out

  
def solve_file(file_path,ef_template):
    if ef_template=='None':
        cmd = ["python3", CUR_DIR + "/prover.py", "--engine", METHOD, "--lang", LANG,"--file", file_path]
    else:
        cmd = ["python3", CUR_DIR + "/prover.py", "--engine", METHOD, "--lang", LANG, "--template", ef_template ,"--file", file_path]
    out = solve_with_bin_solver(cmd, MAXTIME)
    lines = out.split('\n')
    print(lines)
    return parsing_out(file_path,ef_template,lines,mode=METHOD)
    
    

def three_method_compare(root,num_of_thread):
    file_list=[]
    
    result_dir='./result'
    
    if not os.path.isdir("result"):
        os.mkdir("result")
    # get all .smt2 [chc format]
    for dirpath, _, filenames in os.walk(root):
        for filename in filenames:
            if filename.endswith('.smt2'):
                file_path = os.path.join(dirpath, filename)
                file_list.append(file_path)
                
    if METHOD=='efsmt':
        templates=all_template
    else:
        templates=['None']
    
    def multi_func(files,result_queue):
        result_list=[]
        for file in files:
            print(file)
            relative_path = os.path.relpath(file, root)
            no_ext_path, _ = os.path.splitext(relative_path)
            new_path = os.path.join(result_dir, no_ext_path)
            new_dir = os.path.dirname(new_path)
            if not os.path.exists(new_dir):
                os.makedirs(new_dir)
            
            for template in templates:
                save_path=new_path+"_"+str(template)+".json"
                result=solve_file(file,template)
                result['origin_relpath']=relative_path
                with open(save_path, 'w') as f:
                    json.dump(result,f,indent=4)
                result_list.append(result)
        result_queue.put(result_list)
    
    num_of_file = len(file_list) //num_of_thread
    remainder = len(file_list) % num_of_thread
    processes = []
    result_queue = Queue() 

    for i in range(num_of_thread):
        start_index = i * num_of_file + min(i, remainder)
        end_index = (i + 1) * num_of_file + min(i + 1, remainder)
        process = Process(target=multi_func, args=(file_list[start_index:end_index],result_queue))
        process.start()
        processes.append(process)
    
    all_results = []
    for _ in range(num_of_thread):
        all_results.extend(result_queue.get()) 
        
    for process in processes:
        process.join()
    # for file_path in file_list:
    #     relative_path = os.path.relpath(file_path, root)
    #     no_ext_path, _ = os.path.splitext(relative_path)
    #     new_path = os.path.join(result_dir, no_ext_path)
    #     new_dir = os.path.dirname(new_path)
        
        # if not os.path.exists(new_dir):
        #     os.makedirs(new_dir)
        
    #     new_path+="_"+str(METHOD)+"_"+str(LANG)
    #     if METHOD!='efsmt':
    #         save_path=new_path+".json"
    #         result = solve_file(file_path,'None')
    #         with open(save_path, 'w') as f:
    #             json.dump(result,f,indent=4)
    #         result_list.append(result)
    #     else:
    #         for template in all_template:
    #             save_path=new_path+"_"+str(template)+".json"
    #             result=solve_file(file_path,template)
    #             with open(save_path, 'w') as f:
    #                 json.dump(result,f,indent=4)
    #             result_list.append(result)
    
    
    data_process(all_results)
    return

def Initial():
    if LANG not in ['chc','sygus']:
        print("Unexpected language used in verfication.")
    if METHOD not in ['kind','pdr','efsmt']:
        print("Unexpected method used in verfication.")
    if LANG=='sygus' and METHOD=='kind':
        print("do not combine sygus and kind, which is not a valid combination")
        return False
    return True

# 
if __name__ == "__main__":
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('-l','--lang',type=str,nargs='+',default=LANG)
    parser.add_argument('-m','--method',type=str,nargs='+',default=METHOD)
    parser.add_argument('-p','--goal_path',default=GOAL_PATH)
    parser.add_argument('-ns','--nosafe',action='store_true')
    parser.add_argument('-t','--time',default=MAXTIME)
    parser.add_argument('-th','--thread',default=cpu_count())
    args=parser.parse_args()
    
    MAXTIME=int(args.time)
    print("Used Thread Number",cpu_count())
    if not args.nosafe:
        GOAL_PATH=args.goal_path
        for Language,Method in itertools.product(args.lang,args.method):
            LANG=Language
            METHOD=Method
            run=Initial()
            if run:
                three_method_compare(CUR_DIR + GOAL_PATH, int(args.thread))
    
    
