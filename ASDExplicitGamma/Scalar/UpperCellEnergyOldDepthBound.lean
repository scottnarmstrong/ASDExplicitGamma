module

public import ASDExplicitGamma.Scalar.UpperCellEnergyOldTraceFrame
public import ASDExplicitGamma.Native.OldSignedAffineReciprocal

/-! The actual OLD descendant response norms are paid by the same trace
majorant used for the sensitivity parameter. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Variational Native Algsuperdiff.Section3
noncomputable section

/-- The inverse OLD history discount is exactly the square-root depth cost
in the sensitivity envelope. -/
theorem upper_cell_history_depth_cost (j : ℕ) :
    Real.sqrt ((Real.sqrt 3)^j) = (inverseHistoryDiscount⁻¹)^j := by
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    ←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3),
    ←Real.rpow_mul (by norm_num : (0:ℝ)≤3),
    inverse_history_discount_eq,inv_inv,
    ←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  congr 1
  ring

/-- A physical descendant costs precisely the inverse geometric history weight. -/
theorem upper_cell_old_descendant_norm_bound
    (M : ABKModel 2) (n ell : ℤ) (ω : Cutoff.CutoffSample 2)
    (j : ℕ) (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth (originCube 2 (n-ell)) j) :
    fullResponseOperatorNorm R
      ((Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun) ≤
      (inverseHistoryDiscount⁻¹)^j * (1+2*(lagTraceHistory M n ell ω).toReal+
        Real.sqrt (2*(lagTraceHistory M n ell ω).toReal)) := by
  let Q := originCube 2 (n-ell)
  let a := (Annealed.sigmaBar M n:ℝ)⁻¹ • (Cutoff.coefficientCutoff M.nu n ω).toFun
  obtain ⟨Lam,hEll⟩ := upper_cell_old_normalized_elliptic M n Q ω
  have ho := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  have hd := old_signed_response_depth_discount_bound Q a ho j
  have ha := pow_pos inverse_history_discount_range.1 j
  have hb : fullResponseDepthMax Q a j ≤ oldSignedResponseHistory Q a /
      inverseHistoryDiscount^j := (le_div_iff₀ ha).2 (by simpa only [mul_comm] using hd)
  have hm := upper_cell_old_response_history_majorant M n ell ω
  calc
    _ ≤ fullResponseDepthMax Q a j := full_response_norm_le_depth_max Q R a j hR
    _ ≤ oldSignedResponseHistory Q a / inverseHistoryDiscount^j := hb
    _ ≤ (1+2*(lagTraceHistory M n ell ω).toReal+
        Real.sqrt (2*(lagTraceHistory M n ell ω).toReal))/inverseHistoryDiscount^j :=
      div_le_div_of_nonneg_right hm ha.le
    _ = _ := by rw [div_eq_mul_inv,inv_pow,mul_comm]

end
end ASDExplicitGamma.Scalar
