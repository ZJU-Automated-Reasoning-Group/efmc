import argparse
import os
import json
import csv
import seaborn as sns
import itertools
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
from collections import defaultdict, Counter
import re


def is_isolated_word(word, text):
    return re.search(rf'\b{word}\b', text) is not None


all_solver = ['z3', 'cvc5', 'btor', 'yices2', 'mathsat', 'bitwuzla']
all_bit_blasting_solver = ['z3qbf', 'caqe', 'q3b', 'cd15', 'lgl',
                           'mc']
all_cegis_solver = ['cegis_z3', 'cegis_msat',
                    'cegis_yices', 'cegis_btor', 'cegis_cvc4']
CUR_DIR = os.path.dirname(os.path.realpath(__file__))
SAVEDIR = CUR_DIR + "/Result"


class Experiment_Helper:
    def __init__(self, data_list) -> None:
        self.data = data_list

    def generate_row_elements(self, entry):
        row_elements = []

        if 'smt_solver' in entry and entry['smt_solver'] != 'cegis':
            row_elements.append(entry['smt_solver'])
        elif 'cegis_solver' in entry:
            row_elements.append(entry['cegis_solver'])
        else:
            row_elements.append("")

        if 'method' in entry:
            row_elements.append(entry['method'])
        else:
            row_elements.append("")

        if 'template' in entry:
            row_elements.append(entry['template'])
        else:
            row_elements.append("")

        if 'strengthen' in entry:
            row_elements.append(entry['strengthen'])
        else:
            row_elements.append("False")

        if 'num_disjunctions' in entry:
            row_elements.append(entry['num_disjunctions'])
        else:
            row_elements.append(1)

        return row_elements

    def generate_csv(self, output_filename):
        file_data = defaultdict(dict)
        stats = defaultdict(Counter)
        for entry in self.data:
            row_elements = self.generate_row_elements(entry)
            row_key = tuple(row_elements)
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

            file_data[row_key][entry['file']] = result
            stats[row_key][result] += 1

        with open(output_filename, 'w', newline='') as csvfile:
            csvwriter = csv.writer(csvfile)

            # Collect column names
            column_names = set()
            for results in file_data.values():
                column_names.update(results.keys())
            sorted_column_names = sorted(list(column_names))

            # Write header
            header = ['SMT Solver', 'Method', 'Template',
                      'Strengthen', 'Num Disjunctions'] + sorted_column_names
            csvwriter.writerow(header)

            # Write rows
            for row_key, results in file_data.items():
                row = list(row_key)
                for column_name in sorted_column_names:
                    row.append(results.get(column_name, 'N/A'))
                csvwriter.writerow(row)

            csvwriter.writerow([])
            stats_header = ['SMT Solver', 'Method', 'Template',
                            'Strengthen', 'Num Disjunctions', 'T', 'F', 'Err', 'X', 'N/A']
            csvwriter.writerow(stats_header)
            for row_key, counter in stats.items():
                stats_row = list(row_key)
                for key in stats_header[5:]:
                    stats_row.append(counter[key])
                csvwriter.writerow(stats_row)

    def plot_basic_template(self):
        result = {}
        for entry in self.data:
            if 'num_disjunctions' in entry or 'power' in entry.get('template','') or 'strength' in entry or 'template' not in entry:
                continue
            if entry['template'] in ['bv_interval', 'bv_octagon', 'bv_poly', 'bv_zone']:
                solver = 'CS' + \
                    entry['cegis_solver'] if entry['smt_solver'] == 'cegis' else entry['smt_solver']
                template = entry['template']
                bits = '32bits' if '32bits' in entry['bits'] else '64bits'
                safe = entry.get('safe', False)

                key = (solver, template, bits)
                if key not in result:
                    result[key] = {'correct': 0, 'total': 0}
                result[key]['total'] += 1
                if safe:
                    result[key]['correct'] += 1

        for key in result:
            result[key]['accuracy'] = result[key]['correct'] / \
                result[key]['total']
            print(result[key]['correct'],result[key]['total'])
        accuracy_data = result
        plt.figure(figsize=(12, 6))

        for key, value in accuracy_data.items():
            solver, template, bits = key
            accuracy = value['accuracy']
            label = f"{template} ({bits})"
            plt.plot(solver, accuracy, marker='o', label=label)

        plt.ylabel('Accuracy')
        plt.xticks(rotation=45)
        plt.legend(title='Template & Bits', bbox_to_anchor=(
            1.05, 1), loc='upper left', borderaxespad=0.)
        plt.tight_layout()

        plt.savefig('accuracy_plot.svg', format='svg')
        plt.show()

    def plot_top_10_cumulative_time_and_accuracy(self, output_file, specific_key=None, specific_value=None):
        cumulative_data = {}
        success_count = {}

        for data in self.data:
            if specific_key is not None and data.get(specific_key) != specific_value:
                continue
            method = data["method"]
            template = data.get("template", "None")
            smt_solver = data.get("smt_solver", "None")
            cegis_solver = data.get("cegis_solver", "None")
            num_disjunctions = data.get("num_disjunctions", "None")
            prop_strengthen = data.get("strengthen", "None")

            key = (method, template, smt_solver, cegis_solver,
                   num_disjunctions, prop_strengthen)
            time = data["time"]
            is_success = data.get("safe", False)

            if key not in cumulative_data:
                cumulative_data[key] = [time]
                success_count[key] = 1 if is_success else 0
            else:
                cumulative_data[key].append(cumulative_data[key][-1] + time)
                success_count[key] += 1 if is_success else 0

        success_rate = {
            key: success_count[key] / len(cumulative_data[key]) for key in cumulative_data.keys()}
        top_success_rate_keys = sorted(
            success_rate, key=success_rate.get, reverse=True)[:10]

        linestyles = ['-', '--', '-.', ':', (0, (3, 1, 1, 1)), (0, (3, 5, 1, 5)),
                      (0, (1, 1)), (0, (5, 10)), (0, (5, 5)), (0, (5, 1, 1, 1))]

        plt.figure()
        for i, key in enumerate(top_success_rate_keys):
            times = cumulative_data[key]
            label = " / ".join([str(x) for x in key if x != "None"])
            sns.lineplot(x=list(range(len(times))), y=times,
                         label=label, linestyle=linestyles[i])

        plt.title("Cumulative Time vs. File Index (Top 10 Success Rates)")
        plt.xlabel("File Index")
        plt.ylabel("Cumulative Time (s)")

        plt.figure()
        for i, key in enumerate(top_success_rate_keys):
            times = cumulative_data[key]
            label = " / ".join([str(x) for x in key if x != "None"])
            sns.lineplot(x=list(range(len(times))), y=times,
                         label=label, linestyle=linestyles[i])

        plt.title(
            f"Cumulative Time vs. File Index (Top 10 Success Rates, {specific_key}={specific_value})")
        plt.xlabel("File Index")
        plt.ylabel("Cumulative Time (s)")

        plt.legend(fontsize='small')
        file_suffix = f"_{specific_key}_{specific_value}" if specific_key is not None and specific_value is not None else ""
        plt.savefig(
            os.path.join(output_file, f'cumulative_success_rate{file_suffix}.png'), dpi=600)

        plt.figure()
        for i, key in enumerate(top_success_rate_keys):
            success_ratios = [sum(cumulative_data[key][:j + 1]) / (j + 1)
                              for j in range(len(cumulative_data[key]))]
            label = " / ".join([str(x) for x in key if x != "None"])
            sns.lineplot(x=list(range(len(success_ratios))),
                         y=success_ratios, label=label, linestyle=linestyles[i])

        plt.title(
            f"Cumulative Success Rate vs. File Index (Top 10 Success Rates, {specific_key}={specific_value})")
        plt.xlabel("File Index")
        plt.ylabel("Cumulative Success Rate")

        plt.legend(fontsize='small')
        plt.savefig(
            os.path.join(output_file, f'cumulative_success_rate{file_suffix}.png'), dpi=600)

        print("Top 10 Success Rates:")
        for key in top_success_rate_keys:
            method_str = " / ".join([str(x) for x in key if x != "None"])
            rate = success_rate[key]
            print(f"{method_str}: {rate:.2%}")

        print("All Success Rates (sorted):")
        sorted_success_rate = sorted(
            success_rate.items(), key=lambda x: x[1], reverse=True)
        for key, rate in sorted_success_rate:
            method_str = " / ".join([str(x) for x in key if x != "None"])
            print(f"{method_str}: {rate:.2%}")

    def heat_map_between_teamplte_and_solver(self, output_file='.', specify_smt_solver=[],bits='32bits'):
        method_data = []
        for entry in self.data:
            if entry['method'] == 'efsmt' and bits in entry['bits']:
                result = {
                    'solver': entry['smt_solver'] if entry['smt_solver'] != 'cegis' else 'cegis_' + entry[
                        'cegis_solver'],
                    'template': entry['template'],
                    'time': entry['time'],
                    'success': entry.get('safe', False)
                }
                if result['solver'] in all_solver:
                    result['solver'] = 'QI_' + result['solver']
                elif result['solver'] in all_bit_blasting_solver:
                    result['solver'] = 'BB_' + result['solver']
                elif result['solver'] in all_cegis_solver:
                    result['solver'] = 'CS_' + result['solver']
                if specify_smt_solver and result['solver'] not in specify_smt_solver:
                    continue
                method_data.append(result)

        heatmap_data = {}
        for entry in method_data:
            key = (entry['solver'], entry['template'])
            if key not in heatmap_data:
                heatmap_data[key] = {
                    'success_count': 1 if entry['success'] else 0, 'total_count': 1}
            else:
                heatmap_data[key]['total_count'] += 1
                if entry['success']:
                    heatmap_data[key]['success_count'] += 1

        success_rates = {key: value['success_count'] / value['total_count']
                         for key, value in heatmap_data.items()}
        heatmap_df = pd.DataFrame.from_dict(
            success_rates, orient='index', columns=['success_rate'])
        heatmap_df = heatmap_df.reset_index()
        heatmap_df[['solver', 'template']] = pd.DataFrame(
            heatmap_df['index'].tolist(), index=heatmap_df.index)
        heatmap_df = heatmap_df.pivot_table(values='success_rate', index=[
            'solver'], columns=['template'])

        plt.figure(figsize=(8, 6))
        sns.set(font_scale=0.8)  # Adjust font scale
        # cmap = sns.light_palette(as_cmap=True, start=.5, rot=-.75)  # Use a softer color palette
        sns.heatmap(heatmap_df, annot=True, cmap='YlOrRd', fmt='.1%',
                    linewidths=0.5, linecolor='gray')  # Add linewidths and linecolor
        plt.title("Success Rate Heatmap (Method: efsmt)")
        plt.xlabel("Template")
        plt.ylabel("Solver")
        plt.savefig(os.path.join(output_file, f"heatmap_{bits}.png"), dpi=300)

        plt.figure(figsize=(8, 6))
        sns.set(font_scale=0.8)  # Adjust font scale
        # cmap = sns.light_palette(as_cmap=True, start=.5, rot=-.75)  # Use a softer color palette
        sns.heatmap(heatmap_df, annot=True, cmap='Blues', fmt='.1%',
                    linewidths=0.5, linecolor='gray')  # Add linewidths and linecolor
        plt.title("Success Rate Heatmap (Method: efsmt)")
        plt.xlabel("Template")
        plt.ylabel("Solver")
        plt.savefig(os.path.join(output_file, f"heatmap1_{bits}.png"), dpi=300)

    def box_map(self, output_file):
        boxplot_data = []
        for entry in self.data:
            if entry['method'] == 'efsmt':
                result = {
                    'solver': entry['smt_solver'] if entry['smt_solver'] != 'cegis' else entry['cegis_solver'],
                    'template': entry['template'],
                    'time': entry['time'],
                    'success': entry.get('safe', False)
                }
                boxplot_data.append(result)

        # 将数据转换为 DataFrame
        boxplot_df = pd.DataFrame(boxplot_data)

        # 绘制箱线图
        plt.figure()
        sns.boxplot(data=boxplot_df, x='template', y='time', hue='solver')
        plt.title("Execution Time Box Plot (Method: efsmt)")
        plt.xlabel("Template")
        plt.ylabel("Time (s)")
        plt.savefig(os.path.join(output_file, "boxplot.png"), dpi=300)

    def prop_strengthen_compare(self, output_file):
        efsmt_data = [
            entry for entry in self.data if entry['method'] == 'efsmt']

        # 计算不同组合成功率
        success_rate_data = {}
        for entry in efsmt_data:
            key = (entry['smt_solver'] if entry['smt_solver'] != 'cegis' else entry['cegis_solver'],
                   entry['template'],
                   entry.get('strengthen', False))
            if key not in success_rate_data:
                success_rate_data[key] = {'success_count': 1 if entry.get(
                    'safe') else 0, 'total_count': 1}
            else:
                success_rate_data[key]['total_count'] += 1
                if entry.get('safe'):
                    success_rate_data[key]['success_count'] += 1

        # 将成功率数据转换为 Pandas DataFrame
        success_rate_df = pd.DataFrame.from_dict(
            success_rate_data, orient='index', columns=['success_count', 'total_count'])
        # 添加这一行以创建名为 'index' 的新列
        success_rate_df['index'] = success_rate_df.index
        success_rate_df = success_rate_df.reset_index(
            drop=True)  # 使用 drop=True 以避免在重置索引时创建额外的列
        success_rate_df[['solver', 'template', 'strengthen']] = pd.DataFrame(
            success_rate_df['index'].tolist(), index=success_rate_df.index)
        success_rate_df['success_rate'] = success_rate_df['success_count'] / \
            success_rate_df['total_count']
        success_rate_df['solver_template'] = success_rate_df['solver'] + \
            ' - ' + success_rate_df['template']

        # 创建分组条形图
        plt.figure(figsize=(8, 6))
        sns.set(font_scale=0.8)  # Adjust font scale
        sns.barplot(x='solver_template', y='success_rate',
                    hue='strengthen', data=success_rate_df, palette='RdYlBu')
        plt.title(
            'Success Rate by Solver-Template Combinations and Strengthen Parameter')
        plt.xlabel('Solver - Template Combination')
        plt.ylabel('Success Rate')
        plt.xticks(rotation=45)

        plt.savefig(os.path.join(
            output_file, "grouped_barplot_success_rate.png"), dpi=300, bbox_inches='tight')


def init(mode):
    data_list = []
    for subdir, dirs, files in os.walk(SAVEDIR):

        for file in files:
            # print(file)
            if file.endswith(".json"):
                file_path = os.path.join(subdir, file)
                with open(file_path, "r") as json_file:
                    data = json.load(json_file)
            else:
                continue
            if 1 in mode:
                messages = data.get('message', [])
                if not messages:
                    os.remove(file_path)
                    continue
                all_empty_or_traceback = all(not m.strip() for m in messages) or any(
                    'Traceback' in m for m in messages)
                data['file'] = os.path.splitext(data['file'])[0]
                if all_empty_or_traceback:
                    if data.get('unexpected_error', False) != True:
                        print(
                            f"Unexpected error not found in file: {file_path}")
                        data['unexpected_error'] = True
                    data.pop('unknown', None)
                    data.pop('safe', None)
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

                with open(file_path, "w") as json_file:
                    json.dump(data, json_file, indent=4)
            if 11 in mode:
                # if 'num_disjunctions' in data and data['num_disjunctions'] == 2:
                if 'smt_solver' not in data or data['smt_solver'] == 'g4' or data['smt_solver'] == 'gc4':
                    # if 'num_disjunctions' not in data and 'power' in data.get('template', ''):
                    os.remove(file_path)
                    print(f"{file_path} has been deleted.")
            if 'bits' not in data:
                bits_pattern = re.compile(r'(\d+bits_[un]*signed)')
                bits_str = bits_pattern.search(file_path).group()
                # print(bits_str)
                data['bits'] = bits_str
                if bits_str not in data['file']:
                    data['file'] = data['file'] + "_" + bits_str
            if 'unsigned' in  data['bits']:
                data_list.append(data)
    safe_file = []
    if 12 in mode:
        num_disjunctions_counts = {2: 0, 5: 0, 10: 0}
        method_counts = {'pdr': 0, 'eld': 0}

        for data in data_list:
            if 'num_disjunctions' in data:
                if data['num_disjunctions'] in num_disjunctions_counts:
                    num_disjunctions_counts[data['num_disjunctions']] += 1
            if 'method' in data and data['method'] in method_counts:
                method_counts[data['method']] += 1
        print(num_disjunctions_counts, method_counts)
    for data in data_list:
        if data.get("safe", False) == True:
            safe_file.append(data["file"])

    return data_list, safe_file


def collect_data(chc_dir, strengthen=False, disjunction=0):
    data = {}
    for root, _, files in os.walk(chc_dir):
        for file in files:
            if file.endswith('.json'):
                with open(os.path.join(root, file), 'r') as f:
                    content = json.load(f)
                    if 'unsigned' in content['bits'] and content['method'] == 'efsmt' and content.get('strengthen',
                                                                                                      False) == strengthen and content.get(
                            'num_disjunctions', 0) == disjunction:
                        template = content['template']
                        bits = content['bits']
                        source = root.split('/')[-3]
                        # print(source)
                        solver = content['smt_solver']
                        print(bits)
                        if solver == 'cegis':
                            solver = 'cegis' + content['cegis_solver']
                        if bits not in data:
                            data[bits] = {}
                        if source not in data[bits]:
                            data[bits][source] = {}
                        if template not in data[bits][source]:
                            data[bits][source][template] = {}
                        if solver not in data[bits][source][template]:
                            data[bits][source][template][solver] = {
                                'safe': 0, 'unknown': 0, 'timeout': 0}
                        if 'safe' in content:
                            data[bits][source][template][solver]['safe'] += content['safe']
                        elif 'timeout' in content:
                            data[bits][source][template][solver]['timeout'] += content['timeout']
                        elif 'unknown' in content:
                            data[bits][source][template][solver]['unknown'] += content['unknown']
                        else:
                            data[bits][source][template][solver]['unknown'] += 1
                        # if solver == 'z3' and template == 'bv_octagon' and source == '2022.multi-phase':
                        #     print(file, count)
                        #     count += 1
                        #     print(data[bits][source][template][solver])
    return data


def generate_csv(data, output_file='rq1_basic_four_template_compare.csv'):
    with open(output_file, 'w', newline='') as csvfile:
        csv_writer = csv.writer(csvfile)
        header = ["Bits", "Source", "Template",
                  "Solver", "Safe", "Unknown", "Timeout"]
        csv_writer.writerow(header)

        solver_counts = Counter()
        for bit in data:
            for source in data[bit]:
                for template in data[bit][source]:
                    solvers = data[bit][source][template].keys()
                    for solver in solvers:
                        count = data[bit][source][template][solver]['safe']
                        solver_counts[solver] += count

        top_solvers = solver_counts.most_common(3)
        top_solver_names = [solver for solver, _ in top_solvers]

        for bit in data:
            for source in data[bit]:
                for template in data[bit][source]:
                    for solver in top_solver_names:
                        if solver in data[bit][source][template]:
                            row = [bit, source, template, solver]
                            for stat in ['safe', 'unknown', 'timeout']:
                                count = data[bit][source][template][solver][stat]
                                row.append(count)
                            csv_writer.writerow(row)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Process command line arguments")
    parser.add_argument('--mode', nargs='+', type=int,
                        help='one or more mode numbers')
    parser.add_argument('--disjunction', type=int)
    # 1 -> with initial
    # 11 -> temporary process files
    # 2 -> start experiment and paint the basic data without property strengthen and disjunctions.
    # 3 -> final experiment for solution table:
    args = parser.parse_args()
    data_list, safe_file = init(args.mode)
    data_list = [data for data in data_list if data['file'] in safe_file]
    if 1 in args.mode or 2 in args.mode:
        # print(safe_file)
        # new_data_list = [data for data in data_list if data.get('template',False) and (
        #         data.get("smt_solver") in ['z3', 'z3qbf', 'caqe', 'q3b'] or data.get('cegis_solver') in ['z3'])]
        if 2 in args.mode:
            data_list = [
                data for data in data_list if not data.get('strength')]
            RQ1 = Experiment_Helper(data_list)
            if not os.path.exists(SAVEDIR):
                os.makedirs(SAVEDIR)
            if 21 in args.mode:
                RQ1.generate_csv(os.path.join(SAVEDIR, 'all.csv'))
                RQ1.plot_top_10_cumulative_time_and_accuracy(SAVEDIR)
                RQ1.variouts_images(SAVEDIR)
            if 22 in args.mode:
                RQ1.plot_basic_template()
    if 3 in args.mode:
        # no strengthen and no disjunction template, generate basic csv table and its heat map
        data = collect_data('./Result/chc')
        generate_csv(data, output_file='basic_data.csv')
        RQ1_basic = Experiment_Helper(data_list)
        RQ1_basic.heat_map_between_teamplte_and_solver(bits='32bits')
        RQ1_basic.heat_map_between_teamplte_and_solver(bits='64bits')
    if 4 in args.mode:
        # with strengthen and no disjunction template, generate basic csv table and its heat map
        data = collect_data('./Result/chc', strengthen=True)
        generate_csv(data, output_file='with_strength.csv')
        RQ1_basic = Experiment_Helper(data_list)
        RQ1_basic.heat_map_between_teamplte_and_solver(bits='32bits')
        RQ1_basic.heat_map_between_teamplte_and_solver(bits='64bits')
    if 5 in args.mode:
        # with strengthen and no disjunction template, generate basic csv table and its heat map
        data = collect_data(
            './Result/chc', disjunction=args.disjunction)
        generate_csv(
            data, output_file=f'with_disjunction_{args.disjunction}.csv')
        RQ1_basic = Experiment_Helper(data_list)
        RQ1_basic.heat_map_between_teamplte_and_solver(bits='32bits')
        RQ1_basic.heat_map_between_teamplte_and_solver(bits='64bits')
    if 6 in args.mode:
        choosen_method=['eld','pdr','cvc5sys']
        choosen_template=['none']
        data_list=[data for data in data_list if data['method'] in choosen_method or (data['method']=='efsmt' and data['template']==choosen_method)]
        RQ2=Experiment_Helper()
    # DONE:efsmt方法中，不同模板，求解器组合对应的'safe'验证成功率 【对应热力学图】
    # DONE:所有可选参数组合的验证情况【csv表格】
    # DONE:验证成功率最高的十种方法组合对应的时间累积图，正确率累积图【折线图】
    # DOING:将时间延长至600s，然后重跑上述实验+绘图
    # TODO:对比strengthen有无的结果，由于所有的组合太多，都花在一张图中的效果非常不好，因此需要specify 'z3' solver，有无strengthen的结果。【分组柱状图】
    # TODO:关于disjunctions数量变化，efsmt求解的正确率变化【折线图】
    # DONE:不同类型的图像？比如小提琴图，箱线图等等 【由于排列组合太多，箱线图只能针对一部分数据组合进行绘制，但箱线图可以观察时间的总体趋势】
    # DONE:指定某个solver，method，template，strengthen，num_disjunctions，观察其余最高

    # 2. compare different template and different strategy of template method. [no disjunctions and strengthen]
    #    (1) bv_interval 模板表达式的溢出带来的精度丢失，反而降低了其他模板的精度。
    #    (2) 复杂模板对求解效率的影响，UNK数量变化。
    #    (3)
    # 1. compare other invariant generation engine [no disjunctions and strengthen]
    #   讨论模板方法的优势和劣势，相较于其他方法。
    # 2. explore the influence with disjunction and strengthen [about efficiency and ..]
