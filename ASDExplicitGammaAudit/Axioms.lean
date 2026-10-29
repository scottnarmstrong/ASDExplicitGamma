module

public import ASDExplicitGamma

/-!
# Axiom report

Building this module prints the axioms used by the two main theorems and the three intermediate
theorems of `ASDExplicitGamma/Statements/`. Each must depend on exactly `propext`,
`Classical.choice` and `Quot.sound`; `scripts/check_axioms.py` checks the report.

The module is not imported by the library: a `#print axioms` command runs again on every rebuild
of the module that carries it.
-/

@[expose] public section

#print axioms ASDExplicitGamma.explicit_induction_bounds
#print axioms ASDExplicitGamma.inductionState_of_explicit
#print axioms ASDExplicitGamma.molecular_entrance
#print axioms ASDExplicitGamma.induction_step
#print axioms ASDExplicitGamma.allorder_of_state
