module

public import ASDExplicitGamma.Native.ParentRowBoundaryPanel
public import ASDExplicitGamma.Native.ParentRowFlatRootPanel
public import ASDExplicitGamma.Native.ParentBoundaryWeakMeanSum
public import ASDExplicitGamma.Scalar.InverseHistory

/-! Panel package for the centered parent-boundary sums and the
actual joint and Dirichlet roots consumed by the parent generator assembly. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization Gaussian Main Triadic Cold Algsuperdiff.Section3
noncomputable section

private theorem parent_boundary_weak_mean_slope_nonneg (height : ℕ) :
    0 ≤ parentBoundaryWeakMeanSlope gammaZero height := by
  have hs := parent_boundary_weak_mean_profile_sum
    (gamma := gammaZero) (by norm_num [gammaZero]) le_rfl height
  rw [← hs.2]
  apply mul_nonneg
  · exact sub_nonneg.mpr (pow_le_one₀ Scalar.inverse_history_discount_range.1.le
      Scalar.inverse_history_discount_range.2.le)
  · apply tsum_nonneg
    intro j
    rw [← parent_boundary_weak_mean_depth_profile_eq]
    have hj := parent_boundary_mean_depth_slope_nonneg
      (gamma := gammaZero) (by norm_num [gammaZero]) height j
    change 0 ≤ (3683/2500:ℝ)*Scalar.inverseHistoryDiscount^(2*j)*
      (3:ℝ)^(2*gammaZero*(j:ℝ))*parentBoundaryMeanDepthSlope gammaZero height j
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num : (0:ℝ) ≤ 3683/2500)
          (pow_nonneg Scalar.inverse_history_discount_range.1.le _))
        (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _)) hj

/-- The actual paired centered-boundary charge is paid by the exact stored
fields 6 and 7 after the source weak allowance is compared with fields 15
and 12. The two square-root factors remain distinct. -/
theorem parent_boundary_paired_charge_panel
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1)
    (hweak : (23/100:ℝ) + t*parentBoundaryWeakMeanSlope gammaZero (j.val+1) + (2/10^12:ℝ) ≤
      (parentRowFields j).getD 15 0 + (parentRowFields j).getD 12 0*t) :
    let f := fun k => (parentRowFields j).getD k 0
    let W := (23/100:ℝ) + t*parentBoundaryWeakMeanSlope gammaZero (j.val+1) + (2/10^12:ℝ)
    let X := f 15 + f 12*t
    (∑ i : Fin (j.val+1), (
      2*parentRowBeta n 5
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ))) true * Real.sqrt (theta M*W) +
      2*parentRowBeta n 5
        (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
        (q3ModelLength (n+((i.val+1:ℕ):ℤ))) false * Real.sqrt (2*(theta M*W)))) ≤
      theta M*(2*f 6*Real.sqrt X + 2*f 7*Real.sqrt (2*X)) := by
  intro f W X
  have hWcap : W ≤ X := by
    dsimp only [W, X, f]
    exact hweak
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    have hs := parent_boundary_weak_mean_slope_nonneg (j.val+1)
    exact add_nonneg (add_nonneg (by norm_num) (mul_nonneg ht.1 hs)) (by norm_num)
  have hX0 : 0 ≤ X := hW0.trans hWcap
  have hθ1 : theta M ≤ 1 := cold_theta_le_one M hg
  have hθW : theta M*W ≤ X := by
    calc
      theta M*W ≤ 1*W := mul_le_mul_of_nonneg_right hθ1 hW0
      _ = W := one_mul _
      _ ≤ X := hWcap
  have hθW2 : 2*(theta M*W) ≤ 2*X :=
    mul_le_mul_of_nonneg_left hθW (by norm_num)
  have hrootPlus : Real.sqrt (theta M*W) ≤ Real.sqrt X := Real.sqrt_le_sqrt hθW
  have hrootMinus : Real.sqrt (2*(theta M*W)) ≤ Real.sqrt (2*X) :=
    Real.sqrt_le_sqrt hθW2
  let bp : Fin (j.val+1) → ℝ := fun i => parentRowBeta n 5
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    (q3ModelLength (n+((i.val+1:ℕ):ℤ))) true
  let bm : Fin (j.val+1) → ℝ := fun i => parentRowBeta n 5
    (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
    (q3ModelLength (n+((i.val+1:ℕ):ℤ))) false
  have hbp : (∑ i, bp i) ≤ theta M*f 6 := by
    simpa [bp, f] using
      parent_row_band_beta_panel M h hg n hstate j true
  have hbm : (∑ i, bm i) ≤ theta M*f 7 := by
    simpa [bm, f] using
      parent_row_band_beta_panel M h hg n hstate j false
  have hbp0 : 0 ≤ ∑ i, bp i := by
    apply Finset.sum_nonneg
    intro i hi
    dsimp only [bp, parentRowBeta]
    exact Real.sqrt_nonneg _
  have hbm0 : 0 ≤ ∑ i, bm i := by
    apply Finset.sum_nonneg
    intro i hi
    dsimp only [bm, parentRowBeta]
    exact Real.sqrt_nonneg _
  have hplusFactor :
      (∑ i : Fin (j.val+1), 2*bp i*Real.sqrt (theta M*W)) =
        2*Real.sqrt (theta M*W)*(∑ i, bp i) := by
    calc
      _ = ∑ i : Fin (j.val+1), (2*Real.sqrt (theta M*W))*bp i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hminusFactor :
      (∑ i : Fin (j.val+1), 2*bm i*Real.sqrt (2*(theta M*W))) =
        2*Real.sqrt (2*(theta M*W))*(∑ i, bm i) := by
    calc
      _ = ∑ i : Fin (j.val+1), (2*Real.sqrt (2*(theta M*W)))*bm i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hfactor :
      (∑ i : Fin (j.val+1),
        (2*bp i*Real.sqrt (theta M*W)+2*bm i*Real.sqrt (2*(theta M*W)))) =
        2*Real.sqrt (theta M*W)*(∑ i, bp i)+
          2*Real.sqrt (2*(theta M*W))*(∑ i, bm i) := by
    rw [Finset.sum_add_distrib, hplusFactor, hminusFactor]
  have hplus :
      2*Real.sqrt (theta M*W)*(∑ i, bp i) ≤ theta M*(2*f 6*Real.sqrt X) := by
    calc
      _ ≤ 2*Real.sqrt X*(∑ i, bp i) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrootPlus (by norm_num)) hbp0
      _ ≤ 2*Real.sqrt X*(theta M*f 6) :=
        mul_le_mul_of_nonneg_left hbp
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg X))
      _ = _ := by ring
  have hminus :
      2*Real.sqrt (2*(theta M*W))*(∑ i, bm i) ≤
        theta M*(2*f 7*Real.sqrt (2*X)) := by
    calc
      _ ≤ 2*Real.sqrt (2*X)*(∑ i, bm i) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrootMinus (by norm_num)) hbm0
      _ ≤ 2*Real.sqrt (2*X)*(theta M*f 7) :=
        mul_le_mul_of_nonneg_left hbm
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg (2*X)))
      _ = _ := by ring
  change (∑ i : Fin (j.val+1),
      (2*bp i*Real.sqrt (theta M*W)+2*bm i*Real.sqrt (2*(theta M*W)))) ≤ _
  calc
    _ = 2*Real.sqrt (theta M*W)*(∑ i, bp i)+
        2*Real.sqrt (2*(theta M*W))*(∑ i, bm i) := hfactor
    _ ≤ theta M*(2*f 6*Real.sqrt X)+theta M*(2*f 7*Real.sqrt (2*X)) :=
      add_le_add hplus hminus
    _ = _ := by ring

end
end ASDExplicitGamma.Native
