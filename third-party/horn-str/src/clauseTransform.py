#!/bin/env python3
import automata
from hornClause import *
from z3 import *

class Transform:
    def __init__(self, predicate_name = "V", padding_symbol = "p"):
        self.pre_dict = dict()
        self.pre_name = predicate_name
        self.padding_symbol = padding_symbol

    def alphabet_transform(self, c : HornClause, new_alp : list[str])-> HornClause:
        c.alpha = [i for i in c.alpha if i not in new_alp]
        return c

    def unification_predicate_transformation(self, c: HornClause) -> HornClause:
        new_pres = []
        new_posts = []
        for p in c.pre:
            # Get original domain (parameters) - fix here
            arity = p.decl().arity()
            
            original_domain = tuple(p.decl().domain(i) for i in range(arity))
            
            # Create new domain with String as first parameter
            string_sort = z3.StringSort()
            new_domain = (string_sort,) + original_domain
            
            # Create new function with modified domain
            new_p = z3.Function(
                f"{self.pre_name}_{p.decl().name()}", 
                p.decl().range(),  # Same return type
                *new_domain        # New domain with String added at the beginning
            )
            new_pres.append(new_p)
            if p.decl().name() not in self.pre_dict:
                self.pre_dict[p.decl().name()] = new_p

        for p in c.post:
            if p.decl().name() in self.pre_dict:
                new_post = self.pre_dict[p.decl().name()]
                new_posts.append(new_post)
            else:
                arity = p.decl().arity()
                original_domain = tuple(p.decl().domain(i) for i in range(arity))
                
                # Create new domain with String as first parameter
                string_sort = z3.StringSort()
                new_domain = (string_sort,) + original_domain
                
                # Create new function with modified domain
                new_p = z3.Function(
                    f"{self.pre_name}_{p.decl().name()}", 
                    p.decl().range(),  # Same return type
                    *new_domain        # New domain with String added at the beginning
                )
                new_posts.append(new_p)
                self.pre_dict[p.decl().name()] = new_p
            
        c.pre = new_pres
        c.post = new_posts        
        return c
    
    def solve_the_variables(self, c: HornClause) -> HornClause:
        print("solve_the_variables")
        vars = []
        inx = []

        nvars = []
        ninx = []

        for p in c.pre:
            l = [(p.arg(i), list(self.pre_dict.keys()).index(p.decl().name())) for i in range(p.num_args())]
            for i in l:
                vars.append(i[0])
                inx.append(str(i[1]))

        for p in c.post:
            l = [(p.arg(i), list(self.pre_dict.keys()).index(p.decl().name())) for i in range(p.num_args())]
            for i in l:
                nvars.append(i[0])
                ninx.append(str(i[1]))

        vars_in = [z3.String(f"cl_varin{i}") for i in range(len(list(self.pre_dict.keys())))]
        vars_out = [z3.String(f"cl_varout{i}") for i in range(len(list(self.pre_dict.keys())))]
        if c.varin: 
            in_form = self.create_prefix_formula_list(vars, vars_in)
        else:
            in_form = z3.BoolVal(True)
        if c.varout:
            out_form = self.create_prefix_formula_list(nvars, vars_out)
        else:
            out_form = z3.BoolVal(True)

        c.condition = z3.And(
            c.condition,
            in_form,
            out_form
        )

        return c

    def interleave_transform(self, c: HornClause) -> HornClause:
        if c.varin:
            in_form = self.create_padding_formula_list(c.varin, self.padding_symbol, z3.String("varin"))
        else:
            in_form = z3.BoolVal(True)
        if c.varout:
            out_form = self.create_padding_formula_list(c.varout, self.padding_symbol, z3.String("varout"))
        else:
            out_form = z3.BoolVal(True)
        c.condition = z3.And(
            c.condition,
            in_form, 
            out_form
        )
        return c

    def create_prefix_formula_list(self, X_list: list[z3.SeqRef], varins: list[z3.SeqRef]) -> z3.BoolRef:
        """
        Create formula that states each varin[i] equals A[i] concatenated with X[i]
        
        Args:
            X_list: List of string variables
            A_list: List of prefix strings 
            varins: List of string variables that should equal each prefix + variable
        
        Returns:
            Formula: And(varins[0] == Concat(A[0], X[0]), varins[1] == Concat(A[1], X[1]), ...)
        """
        # if len(X_list) != len(A_list) or len(X_list) != len(varins):
        #     raise ValueError("X_list, A_list, and varins must all have the same length")
        
        conds = []
        for x,  var in zip(X_list, varins):
            # Create condition: var == Concat(a, x)
            conds.append(var == x)
        
        # Return conjunction of all conditions
        return z3.And(*conds) if conds else z3.BoolVal(True)
    

    
    
    def create_padding_formula_list(self,
            var_list: list[z3.SeqRef],
            pad_symbol : str,
            var: z3.SeqRef) -> z3.BoolRef:
        """
        Pad each Xi ∈ X_list to the common max length M using pad Ai,
        then interleave the padded Ti = Xi·Ai into varin:
          varin = T0[0] T1[0] … T(n-1)[0]  T0[1] T1[1] … T(n-1)[1] … 
        Here M is exactly max_i |Xi|.
        """
        M = z3.Int('M')
        k = z3.Int('k')
        conds = []
        
        nx = [z3.String(f"new_x{i}")for i in range(len(var_list))]
        for i, x in enumerate(var_list):
            conds.append(z3.InRe(nx[i], z3.Concat(z3.Re(x), z3.Star(z3.Re(z3.StringVal(pad_symbol))))))
        for i in range(len(var_list)):
            conds.append(z3.Length(nx[i]) == M)
        conds.append(
            z3.Or(*[M == z3.Length(Xi) for Xi in var_list])
        )
        for i in range(len(var_list)):
            conds.append(
            z3.ForAll([k],
                z3.Implies(
                    z3.And(k >= 0, k < M),
                    z3.SubString(var, 2*k+i, 1) == z3.SubString(nx[i], k, 1)
                )
            )
        )
        
        return z3.And(*conds)
      