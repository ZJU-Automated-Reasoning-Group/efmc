def read_all_pcp_instances(filepath):
    """
    Read a file containing multiple PCP instances and parse each one.
    
    Args:
        filepath: Path to the file with multiple PCP instances
        
    Returns:
        list: List of tuples (instance_name, tiles)
              where tiles is a list of pairs (x, y) representing the PCP tiles
    """
    with open(filepath, 'r') as f:
        content = f.read()
    
    # Split the content into individual instance blocks
    # Each instance block is separated by blank lines
    instance_blocks = []
    current_block = []
    
    for line in content.splitlines():
        line = line.strip()
        # Skip comments
        if line.startswith('//'):
            continue
        
        if not line and current_block:  # Empty line and we have a block
            instance_blocks.append(current_block)
            current_block = []
        elif line:  # Non-empty line
            current_block.append(line)
    
    # Don't forget the last block if it exists
    if current_block:
        instance_blocks.append(current_block)
    
    # Parse each instance block
    instances = []
    for block in instance_blocks:
        if len(block) < 4:  # Skip blocks that don't have enough lines
            continue
            
        instance_name = block[0].strip(':')
        # Skip sizes line (block[1])
        top_strings = block[2].split()
        bottom_strings = block[3].split()
        
        # Create tiles as pairs
        tiles = list(zip(top_strings, bottom_strings))
        
        instances.append((instance_name, tiles))
    
    return instances

def pairs_to_chc_smt2_monadic(pairs, instance_name="Instance 1"):
    """
    Convert a list of (g_i, h_i) pairs into a CHC (Constrained Horn Clause)
    SMT-LIB2 string. You can adapt the template below to match your full
    transitions, initial states, etc.
    """
    lines = []
    lines.append(f"; {instance_name}")
    lines.append("(set-logic HORN)")

    lines.append("; Declare the Acc predicate")
    lines.append("(declare-fun Acc (String) Bool)")
    lines.append("")
    lines.append("; Here we show each (g_i, h_i) as a comment and add them to the initial states.")
    
    # Build up a big disjunction for the initial states
    # e.g. (or (and (= X "T") (= Y g_i)) (and (= X "B") (= Y h_i)) ...)
    # That’s just an example: adapt to your actual logic.
    or_clauses = []
    for (g_val, h_val) in pairs:
        # comment
        lines.append(f"; g: {g_val}, h: {h_val}")
        # add piece to disjunction for the initial states:
        # Suppose we want (X="T" & Y=g_val) OR (X="B" & Y=h_val).
        # You might do something else depending on your rules.
        or_clause = f"(and (or (= X \"T\") (= X \"B\")) (or (= Y \"{g_val}\") (= Y \"{h_val}\")))"
        or_clauses.append(or_clause)

    # Combine all pairs into one big OR. 
    # This is just a demonstration of how you might do it; adapt as needed.
    # 
    # For example, if you want to say "if (X,Y) is in that set, then Acc(X,Y)", 
    # you could do:
    # 
    #   (assert
    #     (forall ((X String) (Y String))
    #       (=>
    #         (or (and (= X "T") (= Y g1)) (and (= X "B") (= Y h1))
    #             (and (= X "T") (= Y g2)) (and (= X "B") (= Y h2))
    #             ...)
    #         (Acc X)
    #       )
    #     )
    #   )
    #
    # We'll do that below in a simpler form:

    # Build each pair’s disjunct as 
    #    (and (= X "T") (= Y "g_i")) 
    # or  (and (= X "B") (= Y "h_i"))
    # then all combined in an (or ... ) for the entire set of pairs.
    disjuncts = []
    for (g_val, h_val) in pairs:
        if g_val.startswith(h_val):
            disjuncts.append(f"\n         (= X \"T{g_val.removeprefix(h_val)}\")")
        elif h_val.startswith(g_val):
            disjuncts.append(f"\n         (= X \"B{h_val.removeprefix(g_val)}\")")
    big_or = "(or " + " ".join(disjuncts) + ")"

    lines.append("")
    lines.append("; A possible way to assert that all these pairs are initial states for Acc:")
    lines.append("(assert")
    lines.append("  (forall ((X String))")
    lines.append("    (=>")
    lines.append(f"      {big_or}")
    lines.append("      (Acc X)")
    lines.append("    )")
    lines.append("  )")
    lines.append(")")
    lines.append("")
    lines.append('''\n;bad\n(assert
    (forall ((X String) (Y String))
        (=>
        (or 
            (and
                (= X "T")
                (Acc X)
            )
            (and
                (= X "B")
                (Acc X)
        ))
        false
        )
    )
)
                 ''')
    str = ""
    for (g_val, h_val) in pairs:
        str += f'''(assert
    (forall ((X1 String) (Y1 String) (X String) (Y String) (W String) (W1 String))
        (=>
            (and
                (Acc X)
                (= X (str.++ "B" W))
                (= (str.++ W "{h_val}") (str.++ "{g_val}" W1))
                (str.in_re W (re.* (re.union (str.to_re "0") (str.to_re "1"))))
                (str.in_re W1 (re.* (re.union (str.to_re "0") (str.to_re "1"))))
                (= X1 (str.++ "B" W1))
            )
            (Acc X1)
        )
    )
)

(assert
    (forall ((X1 String) (Y1 String) (X String) (Y String) (W String) (W1 String))
        (=>
            (and
                (Acc X)
                (= X (str.++ "B" W))
                (= (str.++ W "{h_val}" W1) "{g_val}")
                (str.in_re W (re.* (re.union (str.to_re "0") (str.to_re "1"))))
                (str.in_re W1 (re.* (re.union (str.to_re "0") (str.to_re "1"))))
                (= X1 (str.++ "T" W1))
            )
            (Acc X1)
        )
    )
)

(assert
  (forall ((X1 String) (Y1 String) (X String) (Y String) (W String) (W1 String))
    (=>
        (and
          (Acc X)
          (= X (str.++ "T" W))
          (= (str.++ W "{g_val}") (str.++ "{h_val}" W1))
          (str.in_re W (re.* (re.union (str.to_re "0") (str.to_re "1"))))
          (str.in_re W1 (re.* (re.union (str.to_re "0") (str.to_re "1"))))
          (= X1 (str.++ "T" W1))
        )
      (Acc X1)
    )
  )
)

(assert
  (forall ((X1 String) (Y1 String) (X String) (Y String) (W String) (W1 String))
    (=>
        (and
          (Acc X)
          (= X (str.++ "T" W))
          (= (str.++ W "{g_val}" W1) (str.++ "{h_val}"))
          (str.in_re W (re.* (re.union (str.to_re "0") (str.to_re "1"))))
          (str.in_re W1 (re.* (re.union (str.to_re "0") (str.to_re "1"))))
          (= X1 (str.++ "B" W1))
        )
      (Acc X1)
    )
  )
)

'''
    lines.append(str)


    # Finally, check satisfiability
    lines.append("(check-sat)")

    return "\n".join(lines)



def pairs_to_chc_smt2_nonmonadic(pairs, instance_name="Instance 1"):
    """
    Convert a list of (g_i, h_i) pairs into a CHC (Constrained Horn Clause)
    SMT-LIB2 string. You can adapt the template below to match your full
    transitions, initial states, etc.
    """
    lines = []
    lines.append(f"; {instance_name}")
    lines.append("(set-logic HORN)")
  
    lines.append("; Declare the Acc predicate")
    lines.append("(declare-fun Acc (String String) Bool)")
    lines.append("")
    lines.append("; Here we show each (g_i, h_i) as a comment and add them to the initial states.")
    
    # Build up a big disjunction for the initial states
    # e.g. (or (and (= X "T") (= Y g_i)) (and (= X "B") (= Y h_i)) ...)
    # That’s just an example: adapt to your actual logic.
    or_clauses = []
    for (g_val, h_val) in pairs:
        # comment
        lines.append(f"; g: {g_val}, h: {h_val}")
        # add piece to disjunction for the initial states:
        # Suppose we want (X="T" & Y=g_val) OR (X="B" & Y=h_val).
        # You might do something else depending on your rules.
        or_clause = f"(and (or (= X \"T\") (= X \"B\")) (or (= Y \"{g_val}\") (= Y \"{h_val}\")))"
        or_clauses.append(or_clause)

    # Combine all pairs into one big OR. 
    # This is just a demonstration of how you might do it; adapt as needed.
    # 
    # For example, if you want to say "if (X,Y) is in that set, then Acc(X,Y)", 
    # you could do:
    # 
    #   (assert
    #     (forall ((X String) (Y String))
    #       (=>
    #         (or (and (= X "T") (= Y g1)) (and (= X "B") (= Y h1))
    #             (and (= X "T") (= Y g2)) (and (= X "B") (= Y h2))
    #             ...)
    #         (Acc X Y)
    #       )
    #     )
    #   )
    #
    # We'll do that below in a simpler form:

    # Build each pair’s disjunct as 
    #    (and (= X "T") (= Y "g_i")) 
    # or  (and (= X "B") (= Y "h_i"))
    # then all combined in an (or ... ) for the entire set of pairs.
    disjuncts = []
    for (g_val, h_val) in pairs:
        if g_val.startswith(h_val):
            disjuncts.append(f"\n        (and (= X \"T\") (= Y \"{g_val.removeprefix(h_val)}\"))")
        elif h_val.startswith(g_val):
            disjuncts.append(f"\n        (and (= X \"B\") (= Y \"{h_val.removeprefix(g_val)}\"))")
    big_or = "(or " + " ".join(disjuncts) + ")"

    lines.append("")
    lines.append("; A possible way to assert that all these pairs are initial states for Acc:")
    lines.append("(assert")
    lines.append("  (forall ((X String) (Y String))")
    lines.append("    (=>")
    lines.append(f"      {big_or}")
    lines.append("      (Acc X Y)")
    lines.append("    )")
    lines.append("  )")
    lines.append(")")
    lines.append("")
    lines.append('''\n;bad\n(assert
    (forall ((X String) (Y String))
        (=>
        (or 
            (and
                (= X "T")
                (= Y "")
                (Acc X Y)
            )
            (and
                (= X "B")
                (= Y "")
                (Acc X Y)
        ))
        false
        )
    )
)
                 ''')
    str = ""
    for (g_val, h_val) in pairs:
        str += f'''(assert
    (forall ((X1 String) (Y1 String) (X String) (Y String) (W String) (W1 String))
        (=>
            (and
                (Acc X Y)
                (= X "B")
                (= Y W)
                (= (str.++ W "{h_val}") (str.++ "{g_val}" W1))
                (str.in_re W (re.* (re.union (str.to_re "0") (str.to_re "1"))))
                (str.in_re W1 (re.* (re.union (str.to_re "0") (str.to_re "1"))))
                (= X1 "B")
                (= Y1 W1)
            )
            (Acc X1 Y1)
        )
    )
)

(assert
    (forall ((X1 String) (Y1 String) (X String) (Y String) (W String) (W1 String))
        (=>
            (and
                (Acc X Y)
                (= X "B")
                (= Y W)
                (= (str.++ W "{h_val}" W1) "{g_val}")
                (str.in_re W (re.* (re.union (str.to_re "0") (str.to_re "1"))))
                (str.in_re W1 (re.* (re.union (str.to_re "0") (str.to_re "1"))))
                (= X1 "T")
                (= Y1 W1)
            )
            (Acc X1 Y1)
        )
    )
)

(assert
  (forall ((X1 String) (Y1 String) (X String) (Y String) (W String) (W1 String))
    (=>
        (and
          (Acc X Y)
          (= X "T")
          (= Y W)
          (= (str.++ W "{g_val}") (str.++ "{h_val}" W1))
          (str.in_re W (re.* (re.union (str.to_re "0") (str.to_re "1"))))
          (str.in_re W1 (re.* (re.union (str.to_re "0") (str.to_re "1"))))
          (= X1 "T")
          (= Y1 W1)
        )
      (Acc X1 Y1)
    )
  )
)

(assert
  (forall ((X1 String) (Y1 String) (X String) (Y String) (W String) (W1 String))
    (=>
        (and
          (Acc X Y)
          (= X "T")
          (= Y W)
          (= (str.++ W "{g_val}" W1) (str.++ "{h_val}"))
          (str.in_re W (re.* (re.union (str.to_re "0") (str.to_re "1"))))
          (str.in_re W1 (re.* (re.union (str.to_re "0") (str.to_re "1"))))
          (= X1 "B")
          (= Y1 W1)
        )
      (Acc X1 Y1)
    )
  )
)

'''
    lines.append(str)


    # Finally, check satisfiability
    lines.append("(check-sat)")

    return "\n".join(lines)


def write_chc_smt2(chc_smt2, filepath):
    # first check if the directory exists
    import os
    directory = os.path.dirname(filepath)
    if not os.path.exists(directory):
        os.makedirs(directory)

    with open(filepath, 'w') as f:
        f.write(chc_smt2)

if __name__ == "__main__":
    import sys
    category_name = sys.argv[1]
    monadic = sys.argv[2] == "monadic"
    instances = read_all_pcp_instances(f"models/pcp/{category_name}.txt")
    print(f"Read {len(instances)} instances")
    # Print information about each instance
    for i, (name, tiles) in enumerate(instances):
        if monadic:
            folder = f"models/smt2/linear/monadic/{category_name}"
            chc_smt2 = pairs_to_chc_smt2_monadic(tiles, name)
        else:
            folder = f"models/smt2/linear/nonmonadic/{category_name}"
            chc_smt2 = pairs_to_chc_smt2_nonmonadic(tiles, name)
        name = name.replace(" ", "_")
        f_name = f"{folder}/{name}.smt2"
        write_chc_smt2(chc_smt2, f_name)

    print(f"Written problem files into {folder}")

