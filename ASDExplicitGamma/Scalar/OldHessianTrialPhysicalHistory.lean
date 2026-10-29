module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalFrame
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.BankOnePassLocal
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw

/-! Exact bank meaning of the actual OLD history on the large scalar
parent. The physical parent scale and completed frame remain independent. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Zero fresh insertion in the bank is exactly the completed OLD field. -/
theorem old_hessian_bank_old_coefficient (M : ABKModel 2) (m : ℤ)
    (omega : Cutoff.CutoffSample 2) :
    attenuatedCoefficient M m (m+40) (bankPartialInsertionWeights m 1 0) omega=
      (Cutoff.coefficientCutoff M.nu m omega).toFun := by
  have hh := bank_one_pass_partial_coefficient M m 1 (by norm_num) 0 omega
  have hz : (Model.partialInsertedCoefficient M m 0 omega).toFun=
      (Cutoff.coefficientCutoff M.nu m omega).toFun :=
    funext (fun x => old_hessian_partial_zero M m omega x)
  simpa only [Nat.cast_one,add_sub_cancel_right,hz] using hh

/-- Every actual root history in the original sigmaBar_m frame is exactly
the bank's ENNReal history, with the identical OLD coefficient and discount. -/
theorem old_hessian_physical_root_history (M : ABKModel 2) (n m : ℤ)
    (omega : Cutoff.CutoffSample 2) (U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet (originCube 2 n)) :
    bankRootInverseHistory U M m (m+40) (bankPartialInsertionWeights m 1 0) omega=
      ENNReal.ofReal (lemmaVInverseHistory U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
          (oldHessianOldOpenCoefficient n m omega)) ((3:ℝ)^(1/4:ℝ))) := by
  let Q := originCube 2 n
  let a := (Cutoff.coefficientCutoff M.nu m omega).toFun
  let af := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
    (oldHessianOldOpenCoefficient n m omega)
  obtain ⟨ell,hK⟩ := exists_originCube_containing_compact (closure (cubeSet Q))
    (isBounded_cubeSet Q).isCompact_closure
  let Lam := ((2:ℝ)*2*(Model.partialInsertedEntryBound M ell m omega)^2+M.nu^2)/M.nu
  have hz : (Model.partialInsertedCoefficient M m 0 omega).toFun=a :=
    funext (fun x => old_hessian_partial_zero M m omega x)
  have hEll : IsEllipticFieldOn M.nu Lam (openCubeSet U) a := by
    have hp := Model.partialInsertedCoefficient_isEllipticFieldOn M ell m omega
      (show (0:ℝ)≤0 ∧ (0:ℝ)≤1 by norm_num) (measurableSet_openCubeSet U)
      (fun x hx => hK (subset_closure (openCubeSet_subset_cubeSet Q (hU hx))))
    simpa only [hz] using hp
  have hEllF := (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
      (oldHessianOldOpenCoefficient n m omega)).mono (measurableSet_openCubeSet U) hU
  have hMatrix (R : TriadicCube 2) (depth : ℕ) (hR : R ∈ descendantsAtDepth U depth) :
      coarseBlockMatrix (cubeSet R) af=
        frameMatrix (Annealed.sigmaBar M m) (coarseBlockMatrix (cubeSet R) a) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    exact old_hessian_old_open_coarse_frame M n m omega R
      ((openCubeSet_subset_of_mem_descendantsAtDepth hR).trans hU)
  have hh := pureFlux_inverseHistory_frame_eq (q := (3:ℝ)^(1/4:ℝ)) U a af hEll hEllF
    (Annealed.sigmaBar_characterization M m).1 hMatrix
  rw [bank_root_history_physical U M m (m+40) (bankPartialInsertionWeights m 1 0) omega a
    (old_hessian_bank_old_coefficient M m omega) hEll]
  exact congrArg ENNReal.ofReal hh.symm

end
end ASDExplicitGamma.Scalar
