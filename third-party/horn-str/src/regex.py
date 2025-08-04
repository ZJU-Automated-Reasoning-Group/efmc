#!/bin/env python3

"""from automata back to regex"""
import automata
import z3

class ReBuilder(object):
    """Abstract class representing how to build a regular language.
    To be inherited/implemented for a given output type"""

    def get_empty(self):
        """Return empty lang"""
        raise NotImplementedError
    
    def get_epsilon(self):
        """Return empty word"""
        raise NotImplementedError

    def concat(self, a, b):
        """Return the concatenation of a and b"""
        raise NotImplementedError

    def plus(self, a, b):
        """Return the disjunction of a and b"""
        raise NotImplementedError

    def star(self, a):
        """Return the kleene star of a"""
        raise NotImplementedError

    def from_letter(self, a):
        """Return the single letter language"""
        raise NotImplementedError

    def is_empty_regex(self, a):
        """Check if the regex is empty"""
        raise NotImplementedError

class StrBuilder(ReBuilder):

    def get_empty(self):
        return "{}"
    def get_epsilon(self):
        return "ε"
    def concat(self, a, b):
        return a + b
    def plus(self, a, b):
        return f"({a}+{b})"
    def star(self, a):
        return f"({a})*"
    def from_letter(self, a):
        return a


class Z3Builder(ReBuilder):
    def get_empty(self):
        return z3.Empty(z3.ReSort(z3.StringSort()))
    def get_epsilon(self):
        return z3.Re("")
    def concat(self, a, b):
        return z3.Concat(a, b)
    def plus(self, a, b):
        return z3.Union(a, b)
    def star(self, a):
        return z3.Star(a)
    def from_letter(self, a):
        return z3.Re(a)
    
    def simplify_regex(self, expr):
        # Rule: (a · a*) + ε -> a* or ε + (a · a*) -> a*
        if expr.decl().kind() == z3.Z3_OP_RE_UNION:
            left, right = expr.children()
            if left == right:
                return self.simplify_regex(left)
            
            # Case 1: ε + (a · a*)
            if left == z3.Re("") and right.decl().kind() == z3.Z3_OP_RE_CONCAT:
                right_left, right_right = right.children()
                if right_right.decl().kind() == z3.Z3_OP_RE_STAR and right_right.children()[0] == right_left:
                    return z3.Star(self.simplify_regex(right_left))  # Simplifies to a*

            # Case 2: (a · a*) + ε (symmetry of union)
            if right == z3.Re("") and left.decl().kind() == z3.Z3_OP_RE_CONCAT:
                left_left, left_right = left.children()
                if left_right.decl().kind() == z3.Z3_OP_RE_STAR and left_right.children()[0] == left_left:
                    return z3.Star(self.simplify_regex(left_left))  # Simplifies to a*

            # Case 3: (a* · a) + ε
            if right == z3.Re("") and left.decl().kind() == z3.Z3_OP_RE_CONCAT:
                left_left, left_right = left.children()
                if left_left.decl().kind() == z3.Z3_OP_RE_STAR and left_left.children()[0] == left_right:
                    return z3.Star(self.simplify_regex(left_right))  # Simplifies to a*

            # Symmetry: ε + (a* · a)
            if left == z3.Re("") and right.decl().kind() == z3.Z3_OP_RE_CONCAT:
                right_left, right_right = right.children()
                if right_left.decl().kind() == z3.Z3_OP_RE_STAR and right_left.children()[0] == right_right:
                    return z3.Star(self.simplify_regex(right_right))  # Simplifies to a*
            return z3.Union(self.simplify_regex(left), self.simplify_regex(right))
        
        elif expr.decl().kind() == z3.Z3_OP_RE_CONCAT:
            left, right = expr.children()
            if (left) == z3.Re(""):
                return self.simplify_regex(right)
            if right == z3.Re(""):
                return self.simplify_regex(left)
            if self.simplify_regex(left) == self.simplify_regex(right) and self.simplify_regex(left).decl().kind() == z3.Z3_OP_RE_STAR:
                return self.simplify_regex(left)
            return z3.Concat(self.simplify_regex(left), self.simplify_regex(right))
        
        elif expr.decl().kind() == z3.Z3_OP_RE_STAR:
            child = expr.children()[0]
            if child.decl().kind() == z3.Z3_OP_RE_STAR:
                return self.simplify_regex(child)
            return z3.Star(self.simplify_regex(child))
        
        else:
            return (expr)
        
    def is_empty_regex(self, expr):
        # Check if the regular expression is empty
        return z3.is_re(expr) and expr.decl().kind() == z3.Z3_OP_RE_EMPTY_SET

class SMT2Bulder(ReBuilder):
    def get_empty(self):
        return "re.none"
    def get_epsilon(self):
        return "(str.to_re \"\")" 
    def concat(self, a, b):
        return f"(re.++ {a} {b})"
    def plus(self, a, b):
        return f"(re.union {a} {b})"
    def star(self, a):
        return f"(re.* {a})"
    def from_letter(self, a):
        return f"(str.to_re \"{a}\")"


class RegexParser:
    def __init__(self, builder):
        self.builder = builder

    def parse(self, s: str):
        tokens = self.tokenize(s)
        self.tokens = tokens
        self.pos = 0
        result = self.regex()
        if self.pos != len(tokens):
            raise ValueError("Unexpected extra input")
        return result

    def tokenize(self, s):
        tokens = []
        i = 0
        while i < len(s):
            c = s[i]
            if c in '()+*':
                tokens.append(c)
                i += 1
            elif c == 'ε':
                tokens.append('ε')
                i += 1
            elif c == '{' and s[i:i+2] == '{}':
                tokens.append('{}')
                i += 2
            elif c.isalnum() or c in ['_']:
                tokens.append(c)
                i += 1
            elif c.isspace():
                i += 1
            else:
                raise ValueError(f"Invalid character: {c}")
        return tokens

    def peek(self):
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        return None

    def eat(self, expected):
        if self.peek() == expected:
            self.pos += 1
        else:
            raise ValueError(f"Expected {expected}, got {self.peek()}")

    def regex(self):
        term = self.term()
        while self.peek() == '+':
            self.eat('+')
            right = self.term()
            term = self.builder.plus(term, right)
        return term

    def term(self):
        factors = []
        while True:
            atom = self.atom()
            if atom is None:
                break
            factors.append(atom)
        if not factors:
            return self.builder.get_epsilon()
        result = factors[0]
        for f in factors[1:]:
            result = self.builder.concat(result, f)
        return result

    def atom(self):
        tok = self.peek()
        if tok is None or tok in [')', '+']:
            return None
        if tok == '(':
            self.eat('(')
            inner = self.regex()
            self.eat(')')
            if self.peek() == '*':
                self.eat('*')
                return self.builder.star(inner)
            return inner
        elif tok == '{}':
            self.eat('{}')
            return self.builder.get_empty()
        elif tok == 'ε':
            self.eat('ε')
            return self.builder.get_epsilon()
        else:
            self.eat(tok)
            res = self.builder.from_letter(tok)
            if self.peek() == '*':
                self.eat('*')
                return self.builder.star(res)
            return res
        

def test_simple_auto():
    target = automata.MatrixNFA([0], [3], [
        {'A': [1], 'N': [0]}, #0
        {'N': [2], 'B': [3]}, #1
        {'N': [1]}, #2
        {'N': [3]}, #3
    ]) 
    print((target.to_regex(SMT2Bulder())))
    print(target.to_regex(StrBuilder()))
    target.show()
    

def test_aboraab_star():
    target = automata.Kleene(automata.Disjunction(
         automata.SingleWordAcceptor("ab"),
         automata.SingleWordAcceptor("aab"),
    ))
    target = automata.Determinization(target)
    target.show()
    print(target.to_regex(StrBuilder()))

def test_empty():
    target = automata.MatrixNFA(
        ["0"], ["1"],
        {"0": {'n': ["0"], 't': ["1"]},
         "1": {'n': ["1"], 't': ["2"]},
         "2": {'n': ["2"], 't': ["2"]},
        }
    )
    target.show()
    print(target.to_regex(Z3Builder()))

def test_simplify_regex():
    builder = Z3Builder()
    
    # Test case 1: (a · a*) + ε -> a*
    regex1 = builder.plus(builder.concat(builder.from_letter('a'), builder.star(builder.from_letter('a'))), builder.get_epsilon())
    simplified_regex1 = builder.simplify_regex(regex1)
    print(f"Original1: {regex1}")
    print(f"Simplified: {simplified_regex1}")
    
    # Test case 2: ε + (a · a*) -> a*
    regex2 = builder.plus(builder.get_epsilon(), builder.concat(builder.from_letter('a'), builder.star(builder.from_letter('a'))))
    simplified_regex2 = builder.simplify_regex(regex2)
    print(f"Original2: {regex2}")
    print(f"Simplified: {simplified_regex2}")
    
    # Test case 3: (a* · a) + ε -> a*
    regex3 = builder.plus(builder.concat(builder.star(builder.from_letter('a')), builder.from_letter('a')), builder.get_epsilon())
    simplified_regex3 = builder.simplify_regex(regex3)
    print(f"Original3: {regex3}")
    print(f"Simplified: {simplified_regex3}")
    
    # Test case 4: ε + (a* · a) -> a*
    regex4 = builder.plus(builder.get_epsilon(), builder.concat(builder.star(builder.from_letter('a')), builder.from_letter('a')))
    simplified_regex4 = builder.simplify_regex(regex4)
    print(f"Original4: {regex4}")
    print(f"Simplified: {simplified_regex4}")

     # Test case 5: a + a -> a
    regex5 = builder.plus(builder.from_letter('a'), builder.from_letter('a'))
    simplified_regex5 = builder.simplify_regex(regex5)
    print(f"Original5: {regex5}")
    print(f"Simplified: {simplified_regex5}")

    # Test case 6: a * (1 + a * a*)
    regex6 = builder.concat(builder.from_letter('a'), builder.plus(builder.get_epsilon(), builder.concat(builder.from_letter('a'), builder.star(builder.from_letter('a')))))
    simplified_regex6 = builder.simplify_regex(regex6)
    print(f"Original6: {regex6}")
    print(f"Simplified: {simplified_regex6}")

    # Test case 7: (a + b) * c
    regex7 = builder.concat(builder.plus(builder.from_letter('a'), builder.from_letter('b')), builder.from_letter('c'))
    simplified_regex7 = builder.simplify_regex(regex7)
    print(f"Original7: {regex7}")
    print(f"Simplified: {simplified_regex7}")

    # Test case 8: (a + b) * (c + d)
    regex8 = builder.concat(builder.plus(builder.from_letter('a'), builder.from_letter('b')), builder.plus(builder.from_letter('c'), builder.from_letter('d')))
    simplified_regex8 = builder.simplify_regex(regex8)
    print(f"Original8: {regex8}")
    print(f"Simplified: {simplified_regex8}")

    # Test case 9: (a + ε) * b
    regex9 = builder.concat(builder.plus(builder.from_letter('a'), builder.get_epsilon()), builder.from_letter('b'))
    simplified_regex9 = builder.simplify_regex(regex9)
    print(f"Original9: {regex9}")
    print(f"Simplified: {simplified_regex9}")

    # Test case 10: a * (b + c) *
    regex10 = builder.concat(builder.from_letter('a'), builder.star(builder.plus(builder.from_letter('b'), builder.from_letter('c'))))
    simplified_regex10 = builder.simplify_regex(regex10)
    print(f"Original10: {regex10}")

    print(f"Simplified: {simplified_regex10}")

    # Test case 11: a* concat a*
    regex11 = builder.plus(builder.from_letter('a'), builder.concat(builder.star(builder.from_letter('a')), builder.star(builder.from_letter('a'))))
    simplified_regex11 = builder.simplify_regex(regex11)
    print(f"Original11: {regex11}")
    print(f"Simplified: {simplified_regex11}")

if __name__ == "__main__":
    builder = Z3Builder()
    parser = RegexParser(builder)

    # Example: (a+b)*a
    regex_str = "a*"

    z3_expr = parser.parse(regex_str)

    print(z3_expr)
