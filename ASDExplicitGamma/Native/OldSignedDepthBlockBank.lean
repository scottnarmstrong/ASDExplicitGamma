module

public import ASDExplicitGamma.Native.OldSignedPartialInverseHistory
public import ASDExplicitGamma.Inverse.BankDepthBlocks
public import ASDExplicitGamma.Inverse.RawShellBandBankInputs

/-! Actual descendant inverse maxima and their depthwise OLD bank remainders. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Identification with the literal inverse depth maximum in the fixed completed frame. -/
theorem old_signed_depth_block_max_eq (M : ABKModel 2) (n : ℤ) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    bankFiniteRootResponseMax (descendantsAtDepth (originCube 2 n) j) M n (n+(1:ℕ))
      (bankPartialInsertionWeights n 1 t) ω =
    ENNReal.ofReal (lemmaVInverseDepthMax (originCube 2 n)
      (oldSignedPartialFrameField M n 1 t ω) j) := by
  rw [old_signed_partial_inverse_depth M n 1 t ht ω j]
  simp only [Nat.cast_one,add_sub_cancel_right]
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact (closure (cubeSet (originCube 2 n)))
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  exact bank_depth_max_physical (originCube 2 n) M n (n+1) _ ω
    (Model.partialInsertedCoefficient M n t ω).toFun
    (by
      funext x
      simpa only [Nat.cast_one,add_sub_cancel_right,Model.partialInsertedCoefficient,
        RegCoeffField.add_apply,RegCoeffField.smul_apply] using
        raw_shell_partial_coefficient_any M n 1 (by norm_num) t ω x)
    (Model.partialInsertedCoefficient_isEllipticFieldOn M ell n ω ht
      (measurableSet_openCubeSet (originCube 2 n))
      (fun _ hx => hK (subset_closure (openCubeSet_subset_cubeSet _ hx)))) j

end
end ASDExplicitGamma.Native
