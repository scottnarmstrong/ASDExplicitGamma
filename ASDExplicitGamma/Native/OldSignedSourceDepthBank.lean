module

public import ASDExplicitGamma.Native.OldSignedSourceCellFrame
public import ASDExplicitGamma.Native.OldSignedDepthBlockBank

/-! The local inverse bank on every actual source-cell descendant population. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Inverse Variational Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Actual depth-block remainder for a source cell at any paid refinement. -/
def oldSignedSourceDepthRemainder (M : ABKModel 2) (n : ℤ) (t : ℝ)
    (U : TriadicCube 2) (j : ℕ) : Cutoff.CutoffSample 2 → ℝ :=
  inverseBankDepthBlockRemainder .localInverse (descendantsAtDepth U j)
    M n (n+(1:ℕ)) (bankPartialInsertionWeights n 1 t) j

/-- No extra moment input is needed for the actual source-cell block bank. -/
theorem old_signed_source_depth_block_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U.scale=n-(r:ℤ)) (j : ℕ) :
    InverseBankDepthBlockConclusion M .localInverse (descendantsAtDepth U j)
      n (n+(1:ℕ)) (bankPartialInsertionWeights n 1 t) j := by
  have hscale : ∀ V ∈ descendantsAtDepth U j,
      V.scale ≤ n-(j:ℤ) ∧ (n-(j:ℤ))-V.scale ≤ 5 := by
    intro V hV
    have hh := scale_eq_sub_of_mem_descendantsAtDepth hV
    rw [hU] at hh
    omega
  have hcard : (descendantsAtDepth U j).card ≤ 6*9^(45+j) := by
    rw [descendantsAtDepth_card,show (3^2:ℕ)=9 by norm_num]
    exact (pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 9)
      (by omega : j ≤ 45+j)).trans (by omega)
  exact inverse_bank_depth_block M h hM hg .localInverse _ n (n+(1:ℕ))
    (by omega) _ (fun k _ => bank_partial_insertion_weights_bounds n 1 t ht.2 k) j
    hscale hcard hpast (bank_inverse_mean_inputs_of_states M h hM hg n hpast).2

/-- The parent display field has the same physical inverse scaling on every
source descendant. Only its restriction to that cell enters the argument. -/
theorem old_signed_source_inverse_depth (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    lemmaVInverseDepthMax U (oldSignedPartialFrameField M n 1 t ω) j=
      (Annealed.sigmaBar M n:ℝ)*lemmaVInverseDepthMax U
        (Model.partialInsertedCoefficient M n t ω).toFun j := by
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact (closure (cubeSet U))
    (isBounded_cubeSet U).isCompact_closure
  have hEll := Model.partialInsertedCoefficient_isEllipticFieldOn M ell n ω ht
    (measurableSet_openCubeSet U)
    (fun _ hx => hK (subset_closure (openCubeSet_subset_cubeSet U hx)))
  have hσ := (Annealed.sigmaBar_characterization M n).1
  have hFrame := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n)
    M.nu_pos hσ (oldSignedPartialResponseCoefficient n 1 t ω)).mono
      (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  exact pureFlux_inverseDepthMax_frame_eq U _ _ hEll hFrame hσ j (fun V hV => by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube V]
    exact old_signed_source_descendant_frame M n r U hU t ω j V hV)

/-- Identification of the depth bank with the literal source inverse maximum. -/
theorem old_signed_source_depth_block_max_eq (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    bankFiniteRootResponseMax (descendantsAtDepth U j) M n (n+(1:ℕ))
      (bankPartialInsertionWeights n 1 t) ω =
      ENNReal.ofReal (lemmaVInverseDepthMax U (oldSignedPartialFrameField M n 1 t ω) j) := by
  rw [old_signed_source_inverse_depth M n r U hU t ht ω j]
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact (closure (cubeSet U))
    (isBounded_cubeSet U).isCompact_closure
  exact bank_depth_max_physical U M n (n+1) _ ω
    (Model.partialInsertedCoefficient M n t ω).toFun
    (by
      funext x
      simpa only [Nat.cast_one,add_sub_cancel_right,Model.partialInsertedCoefficient,
        RegCoeffField.add_apply,RegCoeffField.smul_apply] using
        raw_shell_partial_coefficient_any M n 1 (by norm_num) t ω x)
    (Model.partialInsertedCoefficient_isEllipticFieldOn M ell n ω ht
      (measurableSet_openCubeSet U)
      (fun _ hx => hK (subset_closure (openCubeSet_subset_cubeSet U hx)))) j

end
end ASDExplicitGamma.Native
