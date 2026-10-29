module

public import ASDExplicitGamma.Native.ParentBoundaryCommonKernelPolynomial
public import ASDExplicitGamma.Cold.NativeStrongHistory
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Exact convergent geometric clocks for the complete common-centered source history. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Cold Algsuperdiff.Section3
noncomputable section

/-- The literal ratio for a source quartic degree and physical frame growth. -/
def parentBoundaryCommonHistoryRatio (gamma growth : ℝ) (degree : Fin 5) : ℝ :=
  coldHistoryBeta*(3:ℝ)^(growth*gamma)*(1/3:ℝ)^degree.val

/-- Every source ratio, including growth8, is strictly subcritical on the
entire campaign gamma interval. -/
theorem parent_boundary_common_history_ratio_range
    {gamma : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero)
    (growth : ℝ) (hgrowth : growth ≤ 8) (degree : Fin 5) :
    0 ≤ parentBoundaryCommonHistoryRatio gamma growth degree ∧
      parentBoundaryCommonHistoryRatio gamma growth degree < 1 := by
  have hbase : 0 ≤ coldHistoryBeta*(3:ℝ)^(growth*gamma) :=
    mul_nonneg coldHistoryBeta_pos.le (Real.rpow_nonneg (by norm_num) _)
  have hz : (1/3:ℝ)^degree.val ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hq : parentBoundaryCommonHistoryRatio gamma growth degree ≤ coldHistoryBeta*(3:ℝ)^(8*gamma) := by
    apply (mul_le_mul_of_nonneg_left hz hbase).trans
    rw [mul_one]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
        (mul_le_mul_of_nonneg_right hgrowth hg0)) coldHistoryBeta_pos.le
  have hb : coldHistoryBeta=(3:ℝ)^(-(3/20:ℝ)) := by simpa using cold_native_beta_power 1
  have hmax : coldHistoryBeta*(3:ℝ)^(8*gamma) < 1 := by
    rw [hb,←Real.rpow_add (by norm_num : (0:ℝ)<3)]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<3)
    have hgamma : gamma ≤ 17/50000 := hg
    linarith only [hgamma]
  refine ⟨?_,hq.trans_lt hmax⟩
  unfold parentBoundaryCommonHistoryRatio
  positivity

/-- The exact physical population/frame/degree weight is a geometric power. -/
theorem parent_boundary_common_history_ratio_power
    (gamma growth : ℝ) (degree : Fin 5) (j : ℕ) :
    coldHistoryBeta^j*((1/3:ℝ)^j)^degree.val*(3:ℝ)^(growth*gamma*(j:ℝ))=
      (parentBoundaryCommonHistoryRatio gamma growth degree)^j := by
  rw [Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  have hp : ((1/3:ℝ)^j)^degree.val=((1/3:ℝ)^degree.val)^j := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm]
  rw [hp]
  dsimp only [parentBoundaryCommonHistoryRatio]
  rw [mul_pow,mul_pow]
  ring

/-- The complete affine-geometric raw profile has the source rational sum.
The sign of the affine coefficients is irrelevant to convergence. -/
theorem parent_boundary_common_affine_geometric
    (q U V : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun j : ℕ => q^j*(U+V*(j:ℝ))) ∧
      (∑' j : ℕ,q^j*(U+V*(j:ℝ)))=U/(1-q)+V*q/(1-q)^2 := by
  have hnorm : ‖q‖<1 := by rwa [Real.norm_of_nonneg hq0]
  have h0 := summable_geometric_of_lt_one hq0 hq1
  have h1 : Summable (fun j : ℕ => (j:ℝ)*q^j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have he : (fun j : ℕ => q^j*(U+V*(j:ℝ)))=
      (fun j : ℕ => U*q^j+V*((j:ℝ)*q^j)) := by funext j; ring
  rw [he]
  refine ⟨(h0.mul_left U).add (h1.mul_left V),?_⟩
  rw [(h0.mul_left U).tsum_add (h1.mul_left V),tsum_mul_left,tsum_mul_left,
    tsum_geometric_of_lt_one hq0 hq1,tsum_coe_mul_geometric_of_norm_lt_one hnorm]
  ring

end
end ASDExplicitGamma.Native
