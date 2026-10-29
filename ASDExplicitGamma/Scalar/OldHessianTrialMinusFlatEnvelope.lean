module

public import ASDExplicitGamma.Scalar.OldHessianTrialMinusAffineIdentification
public import ASDExplicitGamma.Scalar.OldHessianTrialMatrixHistoryControl
public import ASDExplicitGamma.Scalar.OldHessianTrialFlatHistoryMoments

/-! The original fine Z energy in the actual completed OLD medium. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Full physical energy of the unchanged fine minus projection, mode by mode. -/
def oldHessianMinusFlatEnergyTerm (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  ∑ i : Fin 2,
    let Z := oldSignedPatchedMinus Q 134 M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 k b L n i
    oldSignedEnergyPairing Q M.nu (Annealed.sigmaBar M m) k Z Z

/-- Genuine full mode convergence and the sharp original affine/oscillation
energy envelope. All quantities are the actual original physical fields. -/
theorem old_hessian_actual_minus_flat_envelope (M : ABKModel 2) (m : ℤ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) :
    Summable (fun n => oldHessianMinusFlatEnergyTerm M m b L n ω) ∧
    (∑' n,oldHessianMinusFlatEnergyTerm M m b L n ω)≤
      oldHessianMinusAffineEnergy M m b L ω+
        2*(Real.sqrt (oldHessianMinusAffineEnergy M m b L ω)*
          Real.sqrt (oldHessianFlatMatrixEnergy M m b L ω))+oldHessianFlatMatrixEnergy M m b L ω := by
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) k
  let O := oldSignedCellAverage Q 134 (fun U => oldSignedResponseHistory U.val a*
    oldSignedFlatOscillationSize Q U.val b L false^2)
  have hh := old_hessian_flat_global_triangle Q 134 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k b L false
  dsimp only at hh
  rw [old_hessian_actual_minus_affine_identification] at hh
  have hO : O≤oldHessianFlatMatrixEnergy M m b L ω := by
    apply old_signed_cell_average_mono
    intro U
    exact mul_le_mul_of_nonneg_right (old_hessian_cell_matrix_history_bounds M m U.val ω).1 (sq_nonneg _)
  refine ⟨hh.1,hh.2.trans ?_⟩
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hO) (Real.sqrt_nonneg _)) (by norm_num : (0:ℝ)≤2))) hO

end
end ASDExplicitGamma.Scalar
