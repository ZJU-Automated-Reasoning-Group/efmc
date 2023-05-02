import argparse
import os
import json
import csv
import seaborn as sns
import itertools
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
from collections import defaultdict
import re

def is_isolated_word(word, text):
    return re.search(rf'\b{word}\b', text) is not None

CUR_DIR = os.path.dirname(os.path.realpath(__file__))
SAVEDIR = CUR_DIR+"/Result"


class Experiment_Helper:
    def __init__(self, data_list) -> None:
        self.data = data_list

    def generate_row_name(self, entry):
        row_name = ""

        if 'smt_solver' in entry and entry['smt_solver'] != 'cegis':
            row_name += '_solver_' + entry['smt_solver']
        elif 'cegis_solver' in entry:
            row_name += '_cegis_solver_' + entry['cegis_solver']

        if 'method' in entry:
            row_name += '_method_' + entry['method']
        if 'template' in entry:
            row_name += '_template_' + entry['template']
        if 'strengthen' in entry:
            row_name += '_strengthen_' + entry['strengthen']
        if 'num_disjunctions' in entry:
            row_name += '_disjunctions_' + entry['num_disjunctions']

        return row_name

    def generate_csv(self, output_filename):
        file_data = defaultdict(dict)

        for entry in self.data:
            row_name = self.generate_row_name(entry)
            result = ""
            if entry.get('safe') == True:
                result = 'T' 
            elif entry.get('safe') == False:
                result = 'F'
            elif entry.get('timeout') == True:
                result = 'X' 
            elif entry.get('unknown') == True:
                result = 'U' 
            elif entry.get('unexpected_error') == True:
                result = 'Err'
            else:
                result = 'N/A'

            file_data[row_name][entry['file']] = result

        with open(output_filename, 'w', newline='') as csvfile:
            csvwriter = csv.writer(csvfile)

            # Collect column names
            column_names = set()
            for results in file_data.values():
                column_names.update(results.keys())
            sorted_column_names = sorted(list(column_names))

            # Write header
            header = [''] + sorted_column_names
            csvwriter.writerow(header)

            # Write rows
            for row_name, results in file_data.items():
                row = [row_name]
                for column_name in sorted_column_names:
                    row.append(results.get(column_name, 'N/A'))
                csvwriter.writerow(row)
    
    @staticmethod
    def generate_row_name(entry):
        row_name=""
        for key in ['smt_solver','method', 'template', 'strengthen', 'num_disjunctions']:
            if key in entry:
                if key == 'smt_solver':
                    if entry['smt_solver']=='cegis':
                        row_name+=f"_cegis_solver_{entry['cegis_solver']}"
                    else:
                        row_name += f"_{key}_{entry[key]}"
                    continue
                row_name += f"_{key}_{entry[key]}"
        return row_name

    def extract_cumulative_time_and_accuracy(self):
        configs = {}
        for entry in self.data:
            row_name = self.generate_row_name(entry)

            if row_name not in configs:
                configs[row_name] = {
                    'times': [0] * len(self.data),
                    'correct': 0,
                }

            index = int(entry['file'].split('_')[-1])  # assuming file names end with an index number
            time = float(entry['time'])
            configs[row_name]['times'][index] += time

            if entry.get('safe') == True:
                configs[row_name]['correct'] += 1

        for config in configs.values():
            config['times'] = np.cumsum(config['times'])

        return configs

    def plot_top_8_cumulative_time_and_accuracy(self, configs,output_file):
        config_rankings = sorted(configs.items(), key=lambda x: x[1]['correct'], reverse=True)[:8]

        df = pd.DataFrame()
        for row_name, data in config_rankings:
            temp_df = pd.DataFrame(data['times'], columns=[row_name])
            df = pd.concat([df, temp_df], axis=1)

        plt.figure(figsize=(12, 6))
        sns.set(style="whitegrid")
        markers = ['o', 'v', 's', 'p', '*', 'D', 'X', 'H']

        ax = sns.lineplot(data=df, dashes=False, markers=markers)
        ax.set(xlabel='File Index', ylabel='Cumulative Time (s)', title='Top 8 Cumulative Time and Accuracy')
        plt.legend(title='Configurations', title_fontsize='13', loc='upper left')
        plt.savefig(output_file)
    

def init():
    
    data_list = []
    for subdir, dirs, files in os.walk(SAVEDIR):
        
        for file in files:
            print(file)
            if file.endswith(".json"):
                file_path = os.path.join(subdir, file)
                with open(file_path, "r") as json_file:
                    data = json.load(json_file)
            else:
                continue
            messages = data.get('message', [])
            all_empty_or_traceback = all(not m.strip() or 'Traceback' in m for m in messages)

            if all_empty_or_traceback:
                if data.get('unexpected_error') != True:
                    print(f"Unexpected error not found in file: {file_path}")
            else:
                if any(is_isolated_word('safe', m) or 'define-fun inv_' in m for m in messages):
                    data['safe'] = True
                elif any(is_isolated_word('infeasible', m) or is_isolated_word('unsat', m) for m in messages):
                    data['safe'] = False
                elif any(is_isolated_word('sat', m) for m in messages):
                    data['safe'] = True
                elif any(is_isolated_word('unknown', m) for m in messages):
                    data['unknown'] = True
                data.pop('unexpected_error', None)
                if 'unknown' not in data:
                    data.pop('unknown', None)
                else:
                    data.pop('safe', None)
                data_list.append(data)
                with open(file_path, "w") as json_file:
                    json.dump(data, json_file, indent=4)
    safe_file = []

    for data in data_list:
        if data.get("safe", False) == True:
            safe_file.append(data["file"])

    return data_list, safe_file



if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Process command line arguments")
    data_list, safe_file = init()
    print(len(data_list))
    data_list = [data for data in data_list if data['file'] in safe_file]
    print(len(data_list))
    # new_data_list = [data for data in data_list if data.get('template',False) and (
    #         data.get("smt_solver") in ['z3', 'z3qbf', 'caqe', 'q3b'] or data.get('cegis_solver') in ['z3'])]
    RQ1=Experiment_Helper(data_list)
    if not os.path.exists(SAVEDIR):
        os.makedirs(SAVEDIR)
    RQ1.generate_csv(os.path.join(SAVEDIR,'rq1.csv'))
    # RQ1.plot_top_8_cumulative_time_and_accuracy(RQ1.extract_cumulative_time_and_accuracy(),os.path.join(SAVEDIR,'rq1.png'))