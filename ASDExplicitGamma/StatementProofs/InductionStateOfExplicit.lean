module

public import ASDExplicitGamma.Bridge.T3
public import ASDExplicitGamma.Statements.ExplicitInductionBounds

/-!
# Proof of `ASDExplicitGamma.inductionState_of_explicit`

The induction state at every scale follows from the explicit induction bounds.
The statement is in `ASDExplicitGamma/Statements/InductionStateOfExplicit.lean`; the proof is assembled here, as
`ASDExplicitGamma.StatementProofs.inductionState_of_explicit`, from proved lemmas.
-/


@[expose] public section

namespace ASDExplicitGamma.StatementProofs

open Algsuperdiff.Section3

/-- ROOT-T3 from the ROOT-T1 conclusion (as a binder). -/
theorem inductionState_of_explicit_of_bounds (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ 17 / 50000) (m0 : ℤ)
    (hT1 : ∀ m : ℤ,
      M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
      (31 / 50) * shellVarianceSum h M.gamma m + (19 / 50) * M.nu ^ 2 ≤
        (Annealed.sigmaBar M m : ℝ) ^ 2 ∧
      (Annealed.sigmaBar M m : ℝ) ^ 2 ≤ M.nu ^ 2 + (13 / 8) * shellVarianceSum h M.gamma m ∧
      AllOrderBounds M m) :
    Algsuperdiff.Frozen.Section3.inductionState M m0 ⟨2 ^ 16, by norm_num⟩ :=
  Bridge.br_t3_induction_state M h hM hγ m0 (fun m _ => hT1 m)

/-- **ROOT-T3.** The induction state, from the ROOT-T1 theorem `explicit_induction_bounds` at every scale. -/
theorem inductionState_of_explicit {M : ABKModel 2} {h : ℝ}
    (hM : PlanarQ3Gaussian M h := by assumption) (hγ : M.gamma ≤ 17 / 50000 := by assumption)
    {m0 : ℤ} :
    Algsuperdiff.Frozen.Section3.inductionState M m0 ⟨2 ^ 16, by norm_num⟩ :=
  inductionState_of_explicit_of_bounds M h hM hγ m0
    (fun m => ASDExplicitGamma.explicit_induction_bounds M h hM hγ m)

end ASDExplicitGamma.StatementProofs
