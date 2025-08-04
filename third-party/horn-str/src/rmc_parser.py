#!/bin/env python3

import automata
import regex
import re
from collections import deque
import networkx as nx
import sys
from collections import defaultdict
from itertools import product


def trans2smt(filename):
    content = ""

    with open(filename,'r',encoding='utf-8') as f:
        for line in f.readlines():
            line = line.strip()
            if line.startswith("//"):
                pass
            else:
                content += line

    ini = re.findall('Initial\s*\{(.*)\}closedUnderTransitions;', content,re.S)
    ini_str = ini[0].strip()
    bad = re.findall('Bad\s*\{(.*)\}\s*.*monolithicWitness;', content,re.S)
    bad_str = bad[0].strip()
    trans = re.findall('Transition\s*\{(.*)\}\s*.*Bad', content,re.S)
    trans_str = trans[0].strip()
    ini_smt = AutomatonModel(ini_str).ini_to_regex()
    bad_smt = AutomatonModel(bad_str).bad_to_regex()
    trans_smt = AutomatonModel(trans_str).to_transducer()
    return ini_smt + "\n\n\n" +  bad_smt + "\n\n\n" + trans_smt

class DFAModel(automata.NFA):
    def __init__(self, alphabet, init, states, trans, accepts):
        super().__init__(alphabet)
        self.size = len(states)
        self.initial = init
        self.transition = trans
        self.final = accepts
        self.graph = dict()

    def getNbStates(self):
        return self.size

    def get_succ(self, src, letter):
        for tran in self.transition:
            if src == tran[0] and letter == tran[1]:
                yield tran[2]

    def get_initial(self):
        yield self.initial

    def is_accepting(self, st):
        return (st in self.final)
    
class AutomatonModel():
    def __init__(self, str) -> None:
        self.str = str
        self.alpha = set()
        self.accepting_states = []
        self.init = []
        self.states = []
        self.trans = []
        self.transition = dict()
        self.alph_dict = dict() 
        self.sequence = list()
        self.loop_trans = dict()
        self.model_str = self.preprocess()

    def preprocess(self):
        for i in self.str.split(";"):
            if i.startswith("init:"):
                self.init = i.split(":")[1].strip()
                self.states.extend(self.init)

            elif i.startswith("accepting:"):
                accepting_state = i.split(":")[1].strip()
                if "," in accepting_state:
                    for i in accepting_state.split(","): 
                        self.accepting_states.append(i.strip())
                else:
                    self.accepting_states.append(accepting_state)
                self.states.extend(self.accepting_states)

            elif "->" in i:
                transition_parts =i.split("->")
                from_state, to_and_symbol = transition_parts[0].strip(), transition_parts[1].strip()
                if not " " in to_and_symbol:
                    to_state = to_and_symbol
                    symbol = ""
                    self.alpha.add("")
                else:
                    to_state, symbol = to_and_symbol.split()
                    if "/" in symbol:
                        for i in symbol.split("/"):
                            self.alpha.add(i)
                    else:
                        self.alpha.add(symbol)
                    self.alpha.add(symbol)

                self.trans.append((from_state, symbol, to_state))

                if from_state == to_state and '/' in symbol:   # self loop
                    if from_state not in self.alph_dict.keys():
                        self.alph_dict[from_state] = symbol
                    else:
                        self.alph_dict[from_state] = self.alph_dict[from_state] + '+' + symbol
                    if from_state not in self.loop_trans.keys():
                        self.loop_trans[from_state] = [(symbol.split("/")[0])]
                    else:
                        self.loop_trans[from_state].append((symbol.split("/")[0]))
                elif from_state == to_state and "" in symbol:
                    if from_state not in self.alph_dict.keys():
                        self.alph_dict[from_state] = "/"
                    else:
                        self.alph_dict[from_state] = self.alph_dict[from_state] + '+' + "/"
                    if from_state not in self.loop_trans.keys():
                        self.loop_trans[from_state] = [("")]
                    else:
                        self.loop_trans[from_state].append((""))
                else:
                    if (from_state, to_state) not in self.transition.keys():
                        self.transition[(from_state, to_state)] = symbol
                    else:
                        self.transition[(from_state, to_state)] = self.transition[(from_state, to_state)] + '+' + symbol


        model = DFAModel(self.alpha, self.init, self.states, self.trans, self.accepting_states)
        return model.to_regex(regex.Z3Builder()).sexpr().replace("\n", "")        
    
    def to_transducer(self):
        G = nx.DiGraph()
        G.add_edges_from(self.transition.keys())
        candicate_paths = []

        for acc in self.accepting_states:
            for path in nx.all_simple_edge_paths(G, self.init, acc):
                candicate_paths.append(path)

        for _ in (nx.simple_cycles(G)):
            raise NotImplementedError("we don't support to parse cycled regular model checking cases")

        transitions = dict()
        for k, v in self.transition.items():
            if "/" not in v:
                transitions[k] = [("", "")]
            else:
                if "+" not in v:
                    transitions[k] = [(v.split("/")[0], v.split("/")[1])]
                else:
                    transitions[k] = [(i.split("/")[0], i.split("/")[1]) for i in v.split("+")]


        res = ""


        for path in candicate_paths:
            inx = 0
            reg_cons = dict()
            input_list = []
            output_list = []
            tmp = []
            for edge in path:
                first_node, second_node = edge[0], edge[1]
                if first_node == self.init and first_node in self.loop_trans.keys():
                    reg_cons[f"reg{inx}"] = (self.loop_trans[first_node])
                    tmp.append([(f"reg{inx}", f"reg{inx}")])
                    inx += 1
                else:
                    tmp.append(transitions[edge])
                    if second_node in self.loop_trans.keys():
                        reg_cons[f"reg{inx}"] = (self.loop_trans[second_node])
                        tmp.append([(f"reg{inx}", f"reg{inx}")])
                        inx += 1


            for i in product(*[[(j[0], j[1]) for j in i] for i in tmp]):
                inner_str = "(assert\n  (forall ((X String) (Y String)"
                for k in reg_cons.keys():
                    inner_str += f" ({k} String)"
                inner_str += ")\n    (=>\n        (and\n          (Acc X)\n          (= X (str.++"
                input_list = [j[0] for j in (list(i))]
                output_list = [j[1] for j in (list(i))]

                for i in input_list:
                    if i in reg_cons.keys():
                        inner_str += f" reg" + i[3:]
                    else:
                        inner_str += f' "{i}"'
                
                inner_str += "))\n          (= Y (str.++"
                for i in output_list:
                    if i in reg_cons.keys():
                        inner_str += f" reg" + i[3:]
                    else:
                        inner_str += f' "{i}"'

                inner_str += "))\n"

                for k, v in reg_cons.items():
                    if len(v) == 1:
                        inner_str += f"          (str.in_re {k} (re.* (str.to_re \"{v[0]}\")))\n"

                    else:
                        inner_str += f"          (str.in_re {k} (re.* (re.union"
                        for rc in v:
                            inner_str += f" (str.to_re \"{rc}\")"
                        inner_str += f")))\n"
                inner_str += f"        )\n      (Acc Y)\n    )\n  )\n)\n"
            res += inner_str

        return res
    
    def ini_to_regex(self):
        result = '(assert\n  (forall ((X String))\n    (=>\n'
        result += f'      (str.in_re X ' + self.model_str + ')\n'
        result += '      (Acc X)\n    )\n  )\n)\n'
        return result
    
    def bad_to_regex(self):
        result = '(assert\n  (forall ((X String))\n    (=>\n      (and\n'
        result += f'      (str.in_re X ' + self.model_str + ')\n'
        result += '        (Acc X)\n      )\n      false\n    )\n  )\n)\n'
        return result


if __name__ == '__main__':
    filename =  sys.argv[1] + ".txt"
    output_name = "../models/smt2/rmc_examples/" + filename[:-4] + ".smt2"
    f = open(output_name, "w")
    f.write("(set-logic HORN)\n\n(declare-fun Acc (String) Bool)\n\n")
    f.write(trans2smt('../models/transducers/' + filename))
    f.write("\n\n(check-sat)")
    f.close()
