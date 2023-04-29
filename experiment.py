import argparse
import os
import json
import csv
import seaborn as sns
import itertools
import matplotlib.pyplot as plt

CUR_DIR = os.path.dirname(os.path.realpath(__file__))
SAVEDIR= CUR_DIR+"/Result"

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


def get_solving_situation_csv(data_list):
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
    
    with open(SAVEDIR + figure_name + ".csv", "w", newline="", encoding="utf-8") as csvfile:
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
def init():
    result_dir = "./Result"
    data_list = []

    for subdir, dirs, files in os.walk(result_dir):
        for file in files:
            if file.endswith(".json"):
                file_path = os.path.join(subdir, file)
                with open(file_path, "r") as json_file:
                    data = json.load(json_file)
                    data_list.append(data)
    safe_file = []

    for data in data_list:
        if data.get("safe", False) == True:
            safe_file.append(data["file"])

    return data_list,safe_file

def get_figure_name(data):
    name = data['file']

    if "template" in data:
        name += f"_template_{data['template']}"
    if "smt_solver" in data:
        name += f"_smt_solver_{data['smt_solver']}"
    if "cegis_solver" in data:
        name += f"_cegis_solver_{data['cegis_solver']}"
    if "strengthen" in data:
        name += f"_strengthen_{data['strengthen']}"
    if "num_disjunctions" in data:
        name += f"_disjunctions_{data['num_disjunctions']}"
    return name

if __name__=="__main__":
    parser = argparse.ArgumentParser(description="Process command line arguments")

    parser.add_argument("--rq1", action="store_true", help="Set rq1 to true")
    parser.add_argument("--rq2", action="store_true", help="Set rq2 to true")
    parser.add_argument("--rq3", action="store_true", help="Set rq3 to true")

    args = parser.parse_args()

    rq1 = args.rq1
    rq2 = args.rq2
    rq3 = args.rq3
    
    data_list,safe_file=init()
    if rq1:
        new_data_list = [data for data in data_list if data.get("method") == "efsmt" and data.get("smt_solver") == "z3"]
        
    if rq2:
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
        plt.savefig(SAVEDIR+figure_name + ".png", dpi=300)

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
    if rq3:
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
            plt.savefig(SAVEDIR+figure_name+"_smt_"+smt_solver+"_template_comp.png",dpi=300)
    
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
            plt.savefig(SAVEDIR+figure_name+"_template_"+template+"_smt_comp.png", dpi=300)