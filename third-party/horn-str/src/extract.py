import re
import sys
import os

def read_last_line(file_path):
    with open(file_path, 'r') as file:
        lines = file.readlines()
        if lines:  # Check if the file is not empty
            return lines[-1].strip()  # Return the last line without trailing spaces or newline
        else:
            return None  # Return None if the file is empty
        
def read_file_omit_lines(file_path, omit_phrase):
    filtered_lines = []
    with open(file_path, 'r') as file:
        for line in file:
            if omit_phrase not in line:  # Check if the line doesn't contain the omit phrase
                filtered_lines.append(line.strip())  # Add the line without trailing spaces or newline
    return filtered_lines


def extract_formulas(file_path, method, name):
    text = ""
    flag = False 

    # First check if "reachable start" is in the file
    reachable_found = False
    with open(file_path, 'r') as file:
        for line in file:
            if "reachable start" in line:
                reachable_found = True
                break
    
    # Exit the program if "reachable start" is not found
    if not reachable_found:
        print(f"Error: 'reachable start' not found in {file_path}")
        print(f"Skipping extraction for {name}")
        sys.exit(0)  # Exit gracefully

        
    with open(file_path, 'r') as file:
        for inx, i in enumerate(file.readlines()):
            if inx == 0:
                len_init = int(i)
            elif inx == 1:
                len_bad = int(i)
            elif inx == 2:
                len_trans = int(i) 
            if "reachable start" in i:
                flag = True
            if "W: RegLan type in model, skipping" not in i and "(get-model)" not in i and flag:
                 text += i
    pattern = re.compile(r'Sending\((\d+)\) \((.*?)\)(?=\nSending\(|\Z)', re.DOTALL)
    matches = pattern.findall(text)
    
    last_line = read_last_line(file_path)
    matches2 = pattern.findall(last_line)
    seq = []

    formulas = {}
    for match in matches + matches2:
        id, formula = match
        if id not in formulas:
            formulas[id] = []
            seq.append(id)
        formulas[id].append(f"({formula})")

    count = 0
    if method != "sat":
        for i in range((len_init)):
            formulas[f"reach_init_{i}"] = formulas.pop(seq[count])
            count = count + 1

        for i in range((len_trans)):
            formulas[f'reach_trans_{i}'] = formulas.pop(seq[count])    
            count = count + 1

        for i in range((len_bad)):
            formulas[f'reach_bad_{i}'] = formulas.pop(seq[count])
            count = count + 1

        for i in range((len_trans)):
            formulas[f'reach_bad_trans_{i}'] = formulas.pop(seq[count])
            count = count + 1

    for i in range(len_init):
        formulas[f'equiv_init_{i}'] = formulas.pop(seq[count])
        count = count + 1
    
    for i in range(len_bad):
        formulas[f'equiv_bad_{i}'] = formulas.pop(seq[count])
        count = count + 1

    for i in range(len_trans):
        formulas[f'equiv_trans_{i}'] = formulas.pop(seq[count])
        count = count + 1
    res = dict()
    for k, v in formulas.items():
        res[k] = v
    #     if "reach" in k:
    #         reach_list.extend(v)
    #     else:
    #         equiv_list.extend(v)
    # res[f'mem_{name}'] = reach_list
    # res[f'equiv_{name}'] = equiv_list

    return res

def divide_pop_push(formula):
    seq = []
    cpattern = re.compile(r'^(.*?)(?=\(push 1\))', re.S)
    cmatches = cpattern.findall(formula)
    context = cmatches[0]
    pattern = re.compile(r'\(push 1\)\s*(.*?)\(pop 1\)', re.DOTALL)
    matches = pattern.findall(formula)

    for i in matches:
        check_sat_count = len(re.findall(r'\(check-sat\)', context + i))
        if check_sat_count > 1:
            tmp = solve_with_reachability_increment(context + i)
            seq.extend(tmp)
        else:
            seq.append(context + i)
    return seq

def solve_with_reachability_increment(text):
    seq = []
    match = re.search(r'^(.*?)\s*(?=\(check-sat\))', text, re.DOTALL)
    main_body = match.group(1)

    seq.append(main_body + "\n(check-sat)\n")
    # Use re.findall to capture each segment ending with (check-sat)
    segments = re.findall(r'(.*?)\s*\(check-sat\)', text, re.DOTALL)

    # Print the segments
    for i, segment in enumerate(segments[1:]):
        main_body += segment
        seq.append(main_body  + "\n(check-sat)\n")
    return seq

def save_formulas_incremental(formulas, output_dir):
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    for id, commands in formulas.items():
        str = ""
        file_path = os.path.join(output_dir, f"{id}.smt2")
        with open(file_path, 'w') as file:
            for command in commands:
                file.write(f"{command}\n")
                str += f"{command}\n"

def save_formulas(formulas, output_dir):
    if not os.path.exists(output_dir):
        os.makedirs(output_dir)
    
    for id, commands in formulas.items():
        str = ""
        # file_path = os.path.join(output_dir, f"{id}.smt2")
        # with open(file_path, 'w') as file:
        for command in commands:
                # file.write(f"{command}\n")
            str += f"{command}\n"
        if id != "length_preservation":
            if str.count("(push 1)") > 0:
                for i, t in enumerate(divide_pop_push(str)):
                    # if not os.path.exists(output_dir+f"/{id}"):
                    #     os.makedirs(output_dir+f"/{id}")
                    with open(os.path.join(output_dir, f"{id}_{i}.smt2"), 'w') as file:
                        file.write(t)

def main(input_file, output_dir, method, name):
    formulas = extract_formulas(input_file, method, name)
    save_formulas_incremental(formulas, output_dir + "/incremental")
    save_formulas(formulas, output_dir + "/non_incremental")


if __name__ == "__main__":
    if len(sys.argv) != 5:
        print("Usage: python script.py <input_file> <output_dir> <method>")
    else:
        input_file = sys.argv[1]
        output_dir = sys.argv[2]
        method = sys.argv[3]
        name = sys.argv[4]
        main(input_file, output_dir, method, name)