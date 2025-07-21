#### Tool Description:

CabPy is a game solver for linear reachability games that exploits cause-effect-relationships in the game graph. The
tool is written in Python 3.

#### Dependencies

- Python 3 and pip
- The GMP library

For instance, these can be installed on Ubuntu with:

```
$ apt-get install python3 python3-pip libgmp3-dev
```

- [PySMT](https://github.com/pysmt/pysmt) (with [MathSAT](https://mathsat.fbk.eu/)
  and [Z3](https://github.com/Z3Prover/z3) installed).
  These can be installed with:

```
$ pip3 install pysmt
$ pysmt-install --msat
$ pysmt-install --z3
```

For the last two commands to work, please make sure that your $PATH variable contains the installation directory of the
pysmt-install script, which will be presented to you after the first command.

#### Usage

CabPy can be used by invoking the following script:

```
$ cab.py -i file.rg
```

See  `cab.py -h` for additional options on debug output.

#### Examples:

We provide several examples in the `examples` folder that can be used as input files, including the newest examples in
the `simple` and `hare` subfolders. The hare example, for instance, encodes the race between the hare and the hedgehog.

To provide a new input game to our tool, the reachability game has to be specified in a .rg file of the following
structure:

```
bool: 'a list of the Boolean variables of the game'
(int or real): 'a list of the variables of the game'
init: 'a formula describing the initial states of the game'
safe: 'a formula describing the moves of the safety player'
reach: 'a formula describing the moves of the reachability player'
goal: 'a formula describing the goal states of the game'
```

We automatically enforce alternation between the players, so it is not necessary to explicitly model this. The formulas
for safe and reach range over lower-case variables (as defined in the lists of variables), which describe the variable
before a move, and upper-case variables describing the variable after a move.
We use the following connectives (ordered in precedence from low to high priority):

```
-> (Implies), <-> (Iff)
| (Or)
& (And)
! (Not)
< (Less than), <= (Less or equal), = (Equal), >= (Greater or equal), > (Greater)
+ (Plus), - (Minus)
```

As an example, consider the Game of Nim played on two heaps with four stones each
(see file 'examples/nim/nim44.rg'):

```
int: x, y
init: x = 4 & y = 4
safe: (X < x & X >= 0 & Y = y) | (Y < y  & Y >= 0 & X = x)
reach: (X < x & X >= 0 & Y = y) | (Y < y  & Y >= 0 & X = x)
goal: x = 0 & y = 0
```

The game in file 'examples/simple/mixed1.rg' is played over both Boolean and integer variables:

```
bool: x
int: z
init: x & z = 0
safe: (X <-> !x) & (Z = z) | (X <-> x) & (Z = z)
reach: !x & Z > z & (X <-> x) | Z = z & (X <-> !x)
goal: z = 5
```

#### Related Publication:

“Causality-Based Game Solving” by Christel Baier, Norine Coenen, Bernd Finkbeiner, Florian Funke, Simon Jantsch and
Julian Siber, Accepted at CAV’21.

Remark: We have observed that the number of subgames for a given benchmark varies
depending on the environment. Subgame computation depends on the Craig interpolants used,
and generally there is no unique interpolant for two unsatisfiable formulas.
We have noticed that the third-party tools we use for SMT solving and
interpolation produce different interpolants in different environments,
resulting in a varying number of subgames.