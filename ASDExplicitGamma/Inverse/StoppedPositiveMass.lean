module

public import ASDExplicitGamma.Inverse.StoppedPositiveTilt
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! The complete positive-label occupancy cost fits the source density floor. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

/-- Literal activation-probability envelope, including the side-squared raw
site count of every aligned activated cube. -/
def positiveOccupancyCost (n : ℕ) : ℝ :=
  (positiveLabelSide n)^2*Real.exp (-1200*positiveLabelSide n*Real.sqrt (positiveLabelSide n))

/-- The full label sequence has a summable geometric majorant. -/
theorem positive_occupancy_majorant (n : ℕ) :
    positiveOccupancyCost n ≤ 9*Real.exp (-6120)*(1/2:ℝ)^n := by
  have hp : (1:ℝ) ≤ 3^n := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3)
  have hs : (3:ℝ) ≤ positiveLabelSide n := by
    unfold positiveLabelSide
    rw [pow_succ]
    nlinarith only [hp]
  have hroot : (17/10:ℝ) ≤ Real.sqrt (positiveLabelSide n) := by
    apply (Real.le_sqrt (by norm_num) (le_trans (by norm_num) hs)).mpr
    linarith only [hs]
  have hg : (51/10:ℝ)*(3:ℝ)^n ≤ positiveLabelSide n*Real.sqrt (positiveLabelSide n) := by
    have hh := mul_le_mul_of_nonneg_left hroot (le_trans (by norm_num) hs)
    unfold positiveLabelSide at hh ⊢
    rw [pow_succ] at hh ⊢
    nlinarith only [hh]
  have h9 : (9:ℝ) ≤ Real.exp 3 := by
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 3) 4
    norm_num [Finset.sum_range_succ,Nat.factorial] at hh
    linarith only [hh]
  have hpow : (9:ℝ)^n ≤ Real.exp (3*(n:ℝ)) := by
    rw [mul_comm (3:ℝ),Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) h9 n
  have hsq : (positiveLabelSide n)^2 = 9*(9:ℝ)^n := by
    unfold positiveLabelSide
    rw [← pow_mul, Nat.mul_comm (n+1) 2,pow_mul,pow_succ]
    norm_num
    ring
  have hbern : 1+2*(n:ℝ) ≤ (3:ℝ)^n := by
    have hh := one_add_mul_le_pow (a := (2:ℝ)) (by norm_num) n
    norm_num at hh
    simpa only [mul_comm] using! hh
  have hexp : 3*(n:ℝ)-6120*(3:ℝ)^n ≤ -6120-(n:ℝ) := by
    nlinarith only [hbern,(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hhalf : Real.exp (-1:ℝ) ≤ 1/2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using!
      one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 2) Real.exp_one_gt_two.le
  calc
    _ ≤ (9*(9:ℝ)^n)*Real.exp (-6120*(3:ℝ)^n) := by
      rw [positiveOccupancyCost,hsq]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith only [hg]
    _ ≤ 9*Real.exp (3*(n:ℝ))*Real.exp (-6120*(3:ℝ)^n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (Real.exp_pos _).le
    _ = 9*Real.exp (3*(n:ℝ)-6120*(3:ℝ)^n) := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
    _ ≤ 9*Real.exp (-6120-(n:ℝ)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
    _ = 9*Real.exp (-6120)*Real.exp (-1:ℝ)^n := by
      rw [← Real.exp_nat_mul,mul_assoc,← Real.exp_add]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.exp_pos _).le hhalf n) (by positivity)

/-- The complete infinite positive occupancy union over all 25 neighboring
roots costs less than exp(-6000), exactly the floor included in q. -/
theorem positive_occupancy_sum :
    25*(∑' n : ℕ, positiveOccupancyCost n) ≤ Real.exp (-6000) := by
  have hg := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_left
    (9*Real.exp (-6120))
  have hs := hg.summable.of_nonneg_of_le (fun n => by unfold positiveOccupancyCost; positivity)
    positive_occupancy_majorant
  have ht := hs.tsum_le_tsum positive_occupancy_majorant hg.summable
  rw [hg.tsum_eq] at ht
  norm_num only at ht
  have h450 : (450:ℝ) ≤ Real.exp 120 := by
    have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 120) 3
    norm_num [Finset.sum_range_succ,Nat.factorial] at hh
    linarith only [hh]
  have hm := mul_le_mul_of_nonneg_right h450 (Real.exp_pos (-6120)).le
  rw [← Real.exp_add] at hm
  norm_num only at hm
  nlinarith only [ht,hm]

end
end ASDExplicitGamma.Inverse
