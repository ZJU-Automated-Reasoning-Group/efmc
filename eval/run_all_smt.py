# coding: utf-8
import csv
import os
import subprocess
import time
import argparse
import sys
from multiprocessing.pool import Pool
import signal
from threading import Timer
import logging

parser = argparse.ArgumentParser()
parser.add_argument('--output', dest='output', default='~/tmp/res', type=str)
parser.add_argument('--timeout', dest='timeout', default=30, type=int, help="timeout for each solving")
parser.add_argument('--workers', dest='workers', default=1, type=int, help="num threads for this file")
parser.add_argument('--dir', dest='dir', default='no', type=str)
parser.add_argument("-v", "--verbose", help="increase output verbosity",
                    action="store_true")

args = parser.parse_args()

if args.verbose:
    logging.basicConfig(level=logging.DEBUG)

m_num_process = args.workers  # thread
out_dir = args.output
g_timeout = args.timeout

m_tools = [
    'tool_name_a --option sth',
    'tool_name_b --option sth',
]


def find_smt2(path):
    flist = []  # path to smtlib2 files
    for root, dirs, files in os.walk(path):
        for fname in files:
            if os.path.splitext(fname)[1] == '.smt2':
                flist.append(os.path.join(root, fname))
    return flist


def split_list(alist, wanted_parts=1):
    length = len(alist)
    return [alist[i * length // wanted_parts: (i + 1) * length // wanted_parts]
            for i in range(wanted_parts)]


def terminate(process, is_timeout):
    if process.poll() is None:
        try:
            process.terminate()
            # os.system("kill -9 " + str(process.pid)) # is this OK?
            is_timeout[0] = True
        except Exception as e:
            print("error for interrupting")
            print(e)


def solve_formulas(flist):
    results = {}
    for tmp_file in flist:
        try:
            m_res = []
            for _ in m_tools:
                m_res.append(-1)

            for k in range(len(m_tools)):
                tool = m_tools[k]
                cmd_tool = []
                for cc in tool.split(' '):
                    cmd_tool.append(cc)
                cmd_tool.append('--file')
                cmd_tool.append(tmp_file)

                logging.debug(cmd_tool)
                # TODO: calculate the time
                start_time = time.time()

                ptool = subprocess.Popen(cmd_tool, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                is_timeout = [False]
                # Give the strfolio process more time to kill z3 binaries first
                timertool = Timer(g_timeout + 3, terminate, args=[ptool, is_timeout])
                timertool.start()
                out_tool = ptool.stdout.readlines()
                out_tool = ' '.join([str(element.decode('UTF-8')) for element in out_tool])

                logging.debug(out_tool)
                ptool.stdout.close()
                timertool.cancel()

                end_time = time.time()
                runtime = end_time - start_time
                # if is_timeout[0] == True:
                m_res[k] = runtime

            results[tmp_file] = m_res
        except Exception as e:
            print(e)
    print("one worker finished!")
    return results


tp = Pool(m_num_process)


def signal_handler(sig, frame):
    tp.terminate()
    print("We are finish here, have a good day!")
    os.system('pkill -9 python')
    os.system('pkill -9 python3')
    sys.exit(0)


signal.signal(signal.SIGINT, signal_handler)


def main():
    flist = find_smt2(args.dir)
    print("Num Files: ", len(flist))
    all_results = []
    files = split_list(flist, m_num_process)
    for i in range(0, m_num_process):
        result = tp.apply_async(solve_formulas, args=(files[i],))
        all_results.append(result)
    tp.close()
    tp.join()
    final_res = []
    for result in all_results:
        final_res.append(result.get())

    # TODO: write results to CSV


if __name__ == "__main__":
    main()
