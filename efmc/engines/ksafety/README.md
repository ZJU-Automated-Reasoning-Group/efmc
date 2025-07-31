# k-safety Verification


## Properties Implemented 

### Non-Interference 

- Purpose: Ensures that low-security outputs do not depend on high-security inputs
- ∀t1, t2. (high1 = high2) → (low1 = low2)
- Implementation: Compares two execution traces where high-security variables are kept equal and checks if low-security variables remain equal



### Determinism

- Purpose: Ensures that for the same inputs, the system always produces the same outputs
- Formula: ∀t1, t2. (inputs1 = inputs2) → (outputs1 = outputs2)
- Implementation: Compares two execution traces with identical inputs and verifies outputs are identical


## Properties Not Implemented 


### Program Equivalence/Refinement

- Purpose: Verify that two program versions are equivalent or that one refines the other
- Types:
  + Functional Equivalence: ∀t1, t2. (inputs1 = inputs2) → (outputs1 = outputs2)
  + Behavioral Refinement: One program's behavior is a subset of another's
  + Semantic Equivalence: Programs compute the same function

### Symmetry Properties

- Purpose: Verify that system behavior is invariant under certain transformations
- Examples:
  + Input Permutation Symmetry: ∀t1, t2. permute(inputs1) = inputs2 → permute(outputs1) = outputs2
  + Parameter Symmetry: Swapping parameters produces equivalent results
  + Geometric Symmetries: Rotational, translational, or reflection symmetries


## More 

- Differential Privacy: ∀t1, t2. |output1 - output2| ≤ ε
- Statistical Independence: Output distributions are independent of certain inputs
- ...?


## Related Work 

[1] Clarkson, M.R. and Schneider, F.B. "Hyperproperties." Journal of Computer Security, 2010.

[2] Clarkson, M.R., Finkbeiner, B., Koleini, M., et al. "Temporal logics for hyperproperties." POST 2014.

[5] Terauchi, T. and Aiken, A. "Secure information flow as a safety problem." SAS 2005.

[6] Clarkson, M.R., Finkbeiner, B., Koleini, M., et al. "Temporal logics for hyperproperties." CAV 2014.

[7] Coenen, N., Finkbeiner, B., Hahn, C., and Hofmann, J. "The hierarchy of hyperlogics." LICS 2019.

[9] Barthe, G., D'Argenio, P.R., and Rezk, T. "Secure information flow by self-composition." Mathematical Structures in Computer Science, 2011.

[10] Unno, H., Terauchi, T., and Koskinen, E. "Constraint-based relational verification." CAV 2021.

[12] Hsu, T.-C., Sánchez, C., and Bonakdarpour, B. "Bounded model checking for hyperproperties." TACAS 2021.

[13] Coenen, N., Finkbeiner, B., Hofmann, J., and Passing, Y. "Safe approximation of hyperproperties using fixpoint iteration." APLAS 2019.

[31] Finkbeiner, B., Hahn, C., Lukert, P., Stenger, M., and Tentrup, L. "Synthesis from hyperproperties." Acta Informatica, 2020.

[33] Coenen, N., Finkbeiner, B., Hahn, C., and Hofmann, J. "The hierarchy of hyperlogics." LICS 2019.