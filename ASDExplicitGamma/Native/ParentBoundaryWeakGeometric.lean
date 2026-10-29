module

public import ASDExplicitGamma.Native.ParentBoundaryMeanDepthProfile
public import ASDExplicitGamma.Scalar.InverseHistory

/-! Exact quarter-power discounted geometric sums for the actual parent weak row. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The source weak-row ratio, including its physical-frame growth. -/
def parentBoundaryWeakRatio (gamma growth : ℝ) (degree : ℕ) : ℝ :=
  inverseHistoryDiscount^2*(3:ℝ)^(growth*gamma)*(1/3:ℝ)^degree

/-- All source weak ratios through growth10 are strictly below one on the
whole campaign gamma interval, including spatial degree zero. -/
theorem parent_boundary_weak_ratio_range {gamma : ℝ}
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (growth : ℝ) (hgrowth : growth ≤ 10) (degree : ℕ) :
    0 ≤ parentBoundaryWeakRatio gamma growth degree ∧
      parentBoundaryWeakRatio gamma growth degree < 1 := by
  have hbase : 0 ≤ inverseHistoryDiscount^2*(3:ℝ)^(growth*gamma) := by positivity
  have hz : (1/3:ℝ)^degree ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hq : parentBoundaryWeakRatio gamma growth degree ≤ inverseHistoryDiscount^2*(3:ℝ)^(10*gamma) := by
    apply (mul_le_mul_of_nonneg_left hz hbase).trans
    rw [mul_one]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
        (mul_le_mul_of_nonneg_right hgrowth hg0)) (sq_nonneg _)
  have ha : inverseHistoryDiscount^2=(3:ℝ)^(-(1/2:ℝ)) := by
    unfold inverseHistoryDiscount
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
    congr 1
    norm_num
  have hmax : inverseHistoryDiscount^2*(3:ℝ)^(10*gamma) < 1 := by
    rw [ha,←Real.rpow_add (by norm_num : (0:ℝ)<3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<3)
    have hgamma : gamma ≤ 17/50000 := hg
    linarith only [hgamma]
  refine ⟨?_,hq.trans_lt hmax⟩
  unfold parentBoundaryWeakRatio
  positivity

/-- The literal quarter-power weight, spatial degree and frame growth
are exactly one geometric power. -/
theorem parent_boundary_weak_ratio_power (gamma growth : ℝ) (degree j : ℕ) :
    inverseHistoryDiscount^(2*j)*((1/3:ℝ)^j)^degree*(3:ℝ)^(growth*gamma*(j:ℝ))=
      parentBoundaryWeakRatio gamma growth degree^j := by
  rw [Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  have hp : ((1/3:ℝ)^j)^degree=((1/3:ℝ)^degree)^j := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm]
  rw [hp,pow_mul]
  dsimp only [parentBoundaryWeakRatio]
  rw [mul_pow,mul_pow]
  ring

/-- Exact complete affine depth sum for each source weak degree. -/
theorem parent_boundary_weak_affine_geometric (gamma growth U V : ℝ) (degree : ℕ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) (hgrowth : growth ≤ 10) :
    Summable (fun j : ℕ => parentBoundaryWeakRatio gamma growth degree^j*(U+V*(j:ℝ))) ∧
      (∑' j : ℕ,parentBoundaryWeakRatio gamma growth degree^j*(U+V*(j:ℝ)))=
        U/(1-parentBoundaryWeakRatio gamma growth degree)+
          V*parentBoundaryWeakRatio gamma growth degree/(1-parentBoundaryWeakRatio gamma growth degree)^2 :=
  parent_boundary_common_affine_geometric _ U V
    (parent_boundary_weak_ratio_range hg0 hg growth hgrowth degree).1
    (parent_boundary_weak_ratio_range hg0 hg growth hgrowth degree).2

end
end ASDExplicitGamma.Native
