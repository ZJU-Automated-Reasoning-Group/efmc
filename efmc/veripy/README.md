# veripy
An auto-active verification library for Python
Work-In-Progress

# Requirements
## Binaries
- [Python 3.6+](https://www.python.org/)
- [Z3](https://github.com/Z3Prover/z3)
## Python Libraries
- [pyparsing](https://github.com/pyparsing/pyparsing)
- [Z3Py](https://pypi.org/project/z3-solver/)

# Features
- [x] Basic verification over ints/bools (assign/if/while/assert/assume)
- [x] Quantifiers in contracts: `forall`, `exists` (typed as `: int`/`: bool`)
- [x] `Havoc` for `while` encoding and weakest preconditions
- [x] Arrays via theory of arrays: `xs[i]`, `xs[i] = v` (functional `store`)
- [ ] Function calls (partial / WIP)
- [ ] More AST mappings

Array support notes:
- Use Python type hints `List[int]` to indicate arrays in specs and inference.
- Indexing `xs[i]` and assignments `xs[i] = v` are modeled with SMT `Select`/`Store`.
- Length `len(xs)` supported in assertions; rich list ops beyond indexing are WIP.

# Related Work

- https://github.com/marcoeilers/nagini: a static verification tool for Python using Viper
- https://github.com/pschanely/CrossHair: a static verification tool for Python using symbolic execution
- 


- https://github.com/JensGM/Typhon