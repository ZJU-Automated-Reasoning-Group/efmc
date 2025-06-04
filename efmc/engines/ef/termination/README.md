# Termination Verification Package

This package provides template-based termination and non-termination verification for bit-vector programs using ranking functions and recurrence sets.

## Package Structure

The package is organized into focused modules:

### Core Modules

- **`result_types.py`** - Result classes (`TerminationResult`, `NonTerminationResult`)
- **`vc_generators.py`** - Verification condition generators (`RankingVCGenerator`, `RecurrenceVCGenerator`)
- **`solvers.py`** - Solver implementations (`RankingSolver`, `RecurrenceSolver`)
- **`validators.py`** - Validation logic (`RankingFunctionValidator`, `RecurrenceSetValidator`)
- **`termination_prover.py`** - Main orchestrator class (`TerminationProver`)
- **`convenience_functions.py`** - High-level convenience functions

## Usage

Import directly from the package:

```python
from efmc.engines.ef.termination import TerminationProver, analyze_termination

# Basic usage
prover = TerminationProver(sts)
prover.set_ranking_template("bv_linear_ranking")
result = prover.prove_termination()

# Comprehensive analysis
results = analyze_termination(sts)
```

## Benefits

1. **Modularity** - Each component has a single responsibility
2. **Maintainability** - Easier to understand and modify individual components  
3. **Testability** - Each module can be tested independently
4. **Extensibility** - Easy to add new solvers, validators, or VC generators
5. **Conciseness** - Focused, readable files without redundancy 