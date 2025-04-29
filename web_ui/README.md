# EFMC & EFSMT Web UI

A web-based user interface for interacting with EFMC (SMT-based Software Model Checking) and EFSMT (Exists-Forall SMT Solver) tools.

## Features

- Modern, responsive web interface
- Code editor with syntax highlighting
- File upload capability
- Example browser
- Real-time verification results
- Support for multiple verification engines
- Configurable timeout settings
- Multiple template options for constraint-based verification
- Customizable SMT solver selection for EFSMT

## Installation

1. Make sure you have EFMC and EFSMT installed and available in your PATH.
2. Install the required Python packages:

```bash
pip install flask werkzeug
```

## Usage

1. Navigate to the web_ui directory:

```bash
cd web_ui
```

2. Run the Flask application:

```bash
python app.py
```

3. Open your web browser and go to:

```
http://localhost:5050
```

## Pages

- **Home**: Overview of the tools and features
- **EFMC**: Interface for running EFMC verification
- **EFSMT**: Interface for solving exists-forall SMT problems
- **About**: Detailed information about the tools and verification engines

## Verification Engines

The EFMC interface supports multiple verification engines:

- **Template-based (Constraint-based)**: Uses constraint solving to generate program invariants based on predefined templates
- **Property-Directed Reachability (PDR)**: Incrementally builds an inductive invariant to prove safety properties
- **K-Induction**: Proves safety properties by induction
- **Houdini**: Infers conjunctive invariants through iterative weakening

## Template Options

For the template-based (constraint-based) engine, the following templates are available:

### Integer/Real Domains
- **Interval**: Simple interval constraints (x ≥ c, x ≤ c)
- **Power Interval**: Interval constraints with powers
- **Zone**: Zone constraints
- **Octagon**: Linear constraints of the form ±x ± y ≤ c
- **Affine**: Affine constraints
- **Power Affine**: Affine constraints with powers
- **Polynomial**: Polynomial constraints
- **Power Polynomial**: Polynomial constraints with powers

### Bitvector Domains
- **BV Interval**: Bit-vector interval constraints
- **Power BV Interval**: Bit-vector interval constraints with powers
- **BV Zone**: Bit-vector zone constraints
- **Power BV Zone**: Bit-vector zone constraints with powers
- **BV Octagon**: Bit-vector octagon constraints
- **Power BV Octagon**: Bit-vector octagon constraints with powers
- **BV Polynomial**: Bit-vector polynomial constraints
- **Power BV Polynomial**: Bit-vector polynomial constraints with powers

## EFSMT Solver Options

The EFSMT interface supports the following SMT solvers:

- **Z3**: Microsoft's Z3 Theorem Prover (default)
- **Z3API**: Z3 API direct access
- **CVC5**: CVC5 SMT Solver
- **Boolector**: Boolector SMT Solver
- **Yices2**: Yices 2 SMT Solver
- **MathSAT**: MathSAT SMT Solver
- **Bitwuzla**: Bitwuzla SMT Solver

## Timeout Settings

Both EFMC and EFSMT interfaces allow you to set a timeout (in seconds) for verification tasks. The default is 60 seconds.

## File Formats

The web UI supports the following file formats:

- `.smt2`: SMT-LIB2 format
- `.sl`: SyGuS format
- `.chc`: Constrained Horn Clauses
- `.sygus`: Syntax-Guided Synthesis

## Development

To modify the web UI:

- HTML templates are in the `templates` directory
- CSS styles are in `static/css/style.css`
- JavaScript code is in `static/js/main.js`

## License

Same as the EFMC project. 