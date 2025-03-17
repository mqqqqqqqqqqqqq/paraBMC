The input files for the experiment are Murphi modeling without invariant protocols, Murphi modeling with invariant protocols.

The output is an invariant test result.

Detecting an invariant in this experiment requires adding the invariant to the protocol's Murphi file.

Run the steps:

1. For example, if you need to detect the mutualEx protocol, you can create a new mutualEx_inv folder and put the Murphi file with the protocol of the invariant to be detected in this folder.

2. Modify the protocol Murphi file path and invariant path in the `/SMT/BMC.py file`, modify `upper_bound` to set the BMC step count, `lower_procount` to set the minimum value for concurrent processes, `upper_procount` to set the maximum value for concurrent processes, and `step_count` to set the process interval.

3. Finally, execute `python SMT/BMC.py`.

In `constructF.py` is the initialization of protocol primitives, rules, invariants, axioms, and so on.

`BMC.py` is the main BMC program algorithm.

`murphi.py` and murphiparser.py are the compilation and conversion interfaces for the syntax.

The types of protocols detected can be **cache coherence** protocols and **distributed protocols**.
