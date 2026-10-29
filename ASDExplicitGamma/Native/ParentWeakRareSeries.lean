module

public import ASDExplicitGamma.Native.ParentWeakTraceNorms

/-! The complete original depth reserve remains proportional to theta. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- Exact combined depth weight for the new theta-linear history payment. -/
theorem parent_weak_rare_weight (M : ABKModel 2) (j : ℕ) :
    inverseHistoryDiscount^(2*j)*inverseBankDepthReserve .localInverse M j*
      parentWeakRareTraceCap M j =
    ((3/10^46:ℝ)*(10:ℝ)^20*theta M)*((3:ℝ)^(-(1/4:ℝ)+2*M.gamma+1/64))^j := by
  have ha := inverse_history_discount_range.1.ne'
  have hw : inverseHistoryDiscount^(2*j)*(inverseHistoryDiscount^j)⁻¹=inverseHistoryDiscount^j := by
    rw [show 2*j=j+j by omega,pow_add,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ ha),mul_one]
  have hn : (9:ℝ)^((j:ℝ)/128)=(3:ℝ)^((j:ℝ)/64) := by
    rw [show (9:ℝ)=(3:ℝ)^2 by norm_num,←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤3)]
    congr 1
    norm_num
    ring
  have hgeo : inverseHistoryDiscount^j*bankDepthFrame M j*(9:ℝ)^((j:ℝ)/128)=
      ((3:ℝ)^(-(1/4:ℝ)+2*M.gamma+1/64))^j := by
    rw [inverse_history_discount_power,bankDepthFrame,hn,
      ←Real.rpow_add (by norm_num : (0:ℝ)<3),←Real.rpow_add (by norm_num : (0:ℝ)<3),
      ←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
    congr 1
    ring
  unfold inverseBankDepthReserve inverseBankReserve parentWeakRareTraceCap
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow]
  calc
    _ = ((3/10^46:ℝ)*(10:ℝ)^20*theta M)*
        ((inverseHistoryDiscount^(2*j)*(inverseHistoryDiscount^j)⁻¹)*bankDepthFrame M j*(9:ℝ)^((j:ℝ)/128)) := by ring
    _ = _ := by rw [hw,hgeo]; norm_num

/-- The theta-linear depth reserve is a genuine summable series, and its
complete normalized sum fits inside the unchanged 1e-12 theta reserve. -/
theorem parent_weak_rare_series_payment (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    Summable (fun j : ℕ => inverseHistoryDiscount^(2*j)*inverseBankDepthReserve .localInverse M j*
      parentWeakRareTraceCap M j) ∧
    (1-inverseHistoryDiscount^2)*(∑' j : ℕ,inverseHistoryDiscount^(2*j)*
      inverseBankDepthReserve .localInverse M j*parentWeakRareTraceCap M j) ≤
        theta M*(1/(2*10^12):ℝ) := by
  let q := (3:ℝ)^(-(1/4:ℝ)+2*M.gamma+1/64)
  let c := (3/10^46:ℝ)*(10:ℝ)^20*theta M
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq : q ≤ 9/10 := by
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      (by norm_num [gammaZero] at hg ⊢; linarith only [hg] : -(1/4:ℝ)+2*M.gamma+1/64 ≤ -(1/8:ℝ))).trans
      parent_weak_three_neg_eighth_le
  have hqn : ‖q‖<1 := by rw [Real.norm_of_nonneg hq0]; linarith only [hq]
  have hs := (summable_geometric_of_norm_lt_one hqn).mul_left c
  have he : (fun j : ℕ => inverseHistoryDiscount^(2*j)*inverseBankDepthReserve .localInverse M j*
      parentWeakRareTraceCap M j)=(fun j : ℕ => c*q^j) :=
    funext (parent_weak_rare_weight M)
  rw [he]
  have hsum : (∑' j : ℕ,q^j) ≤ 10 := by
    rw [tsum_geometric_of_norm_lt_one hqn,←one_div]
    calc
      _ ≤ 1/(1/10:ℝ) := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/10)
        (by linarith only [hq] : (1/10:ℝ)≤1-q)
      _ = 10 := by norm_num
  have hc0 : 0 ≤ c := mul_nonneg (by norm_num) (cold_theta_pos M).le
  have hdis : 1-inverseHistoryDiscount^2 ≤ 1 := sub_le_self _ (sq_nonneg _)
  have hsum0 : 0 ≤ ∑' j : ℕ,c*q^j := tsum_nonneg (fun j => mul_nonneg hc0 (pow_nonneg hq0 j))
  refine ⟨hs,?_⟩
  calc
    _ ≤ ∑' j : ℕ,c*q^j := (mul_le_mul_of_nonneg_right hdis hsum0).trans_eq (one_mul _)
    _ = c*(∑' j : ℕ,q^j) := tsum_mul_left
    _ ≤ c*10 := mul_le_mul_of_nonneg_left hsum hc0
    _ ≤ _ := by
      have hcoef : (3/10^46:ℝ)*(10:ℝ)^20*10 ≤ 1/(2*10^12) := by norm_num
      convert mul_le_mul_of_nonneg_right hcoef (cold_theta_pos M).le using 1 <;> ring

end
end ASDExplicitGamma.Native
