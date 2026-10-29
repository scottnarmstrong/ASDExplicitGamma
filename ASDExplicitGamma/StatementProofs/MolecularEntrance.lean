module

public import ASDExplicitGamma.Scalar.JointMolecularBase

/-!
# Proof of `ASDExplicitGamma.molecular_entrance`

The native induction state holds on a left half-line of scales, by the molecular base case.
The statement is in `ASDExplicitGamma/Statements/MolecularEntrance.lean`; the proof is assembled here, as
`ASDExplicitGamma.StatementProofs.molecular_entrance`, from proved lemmas.
-/

@[expose] public section

namespace ASDExplicitGamma.StatementProofs

open Algsuperdiff.Section3

/-- The molecular base supplies the entrance state on one
completed-label left half-line. The model and amplitude are implicit and the two hypotheses are filled by
`assumption`. -/
theorem molecular_entrance {M : ABKModel 2} {h : ℝ}
    (hM : PlanarQ3Gaussian M h := by assumption) (hγ : M.gamma ≤ gammaZero := by assumption) :
    ∃ K : ℤ, ∀ n : ℤ, n ≤ K → nativeInductionState M h n := by
  obtain ⟨K, hK⟩ := Scalar.joint_molecular_base M h hM hγ
  exact ⟨K, fun n hn => (hK n hn).2⟩

end ASDExplicitGamma.StatementProofs
