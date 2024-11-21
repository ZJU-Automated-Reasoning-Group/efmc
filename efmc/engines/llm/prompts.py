def get_prompt1(cProgram, promptType, previousAns, counterexample):
    if promptType == 0:
        cProgram = cProgram + " Print loop invariants as valid C assertions that help prove the assertion. \
In order to get a correct answer, You may want to consider both the situation of not entering the loop and the situation of jumping out of the loop. \
If some of the preconditions are also loop invariant, you need to add them to your answer as well. \
Use '&&' or '||' if necessary. Don't explain. Your answer should be 'assert(...);'"
    elif promptType == 1:
        cProgram = cProgram + " Print loop invariants as valid C assertions that help prove the assertion. \
Your previous answer '" + previousAns + "'is too strict and not reachable. \
The Reachability of the loop invariant means that the loop invariant I can be derived based on the pre-condition P, i.e. P ⇒ I. \
The following is a counterexample given by z3: " + counterexample + ". \
In order to get a correct answer, You may want to consider the initial situation where the program won't enter the loop. \
Use '&&' or '||' if necessary. Don't explain. Your answer should be 'assert(...);'"
    elif promptType == 2:
        cProgram = cProgram + " Print loop invariants as valid C assertions that help prove the assertion. \
Your previous answer '" + previousAns + "'is too weak and not provable. \
The Provability of the loop invariant means that after unsatisfying loop condition B, we can prove the post-condition Q, i.e. (I ∧ ¬ B) ⇒ Q. \
The following is a counterexample given by z3: " + counterexample + ". \
In order to get a correct answer, you may want to consider the special case of the program executing to the end of the loop. If some of the preconditions are also loop invariant, you need to add them to your answer as well. \
Use '&&' or '||' if necessary. Don't explain. Your answer should be 'assert(...);'"
    elif promptType == 3:
        cProgram = cProgram + " Print loop invariants as valid C assertions that help prove the assertion. \
Your previous answer '" + previousAns + "'is not inductive. \
The Inductive of the loop invariant means that if the program state satisfies loop condition B, the new state obtained after the loop execution S still satisfies, i.e. {I ∧ B} S {I}. \
The following is a counterexample given by z3: " + counterexample + ". \
In order to get a correct answer, You may want to consider the special case of the program executing to the end of the loop. \
Use '&&' or '||' if necessary. Don't explain. Your answer should be 'assert(...);'"
    return cProgram


def get_prompt2(cProgram, promptType, previousAns, counterexample):
    cProgram = cProgram + " Print loop invariants as valid C assertions that help prove the assertion. \
Use '&&' or '||' if necessary. Don't explain. Your answer should be 'assert(...);'"
    return cProgram
