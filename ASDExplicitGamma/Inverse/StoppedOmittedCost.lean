module

public import ASDExplicitGamma.Inverse.StoppedPositiveMass

/-! The full omitted-label activation cost, with the source raw-site factor retained. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
noncomputable section

theorem positive_label_side_ge_three (n : ℕ) : (3:ℝ) ≤ positiveLabelSide n := by
  have hp : (1:ℝ) ≤ 3^n := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3)
  unfold positiveLabelSide
  rw [pow_succ]
  nlinarith only [hp]

theorem positive_label_side_succ (n : ℕ) :
    positiveLabelSide (n+1) = 3*positiveLabelSide n := by
  simp only [positiveLabelSide,pow_succ]
  ring

/-- Each later label costs less than half its predecessor, with all raw
activation sites still included in the side-squared probability envelope. -/
theorem positive_occupancy_cost_succ (n : ℕ) :
    positiveOccupancyCost (n+1) ≤ (1/2:ℝ)*positiveOccupancyCost n := by
  let s := positiveLabelSide n
  let u := positiveLabelSide (n+1)
  have hs : (3:ℝ) ≤ s := positive_label_side_ge_three n
  have hu : u = 3*s := positive_label_side_succ n
  have hroot : (1:ℝ) ≤ Real.sqrt s := (Real.le_sqrt (by norm_num) (by linarith only [hs])).mpr (by nlinarith only [hs])
  have hmono : Real.sqrt s ≤ Real.sqrt u := Real.sqrt_le_sqrt (by nlinarith only [hu,hs])
  have hprod : 3*s*Real.sqrt s ≤ u*Real.sqrt u := by
    rw [hu] at hmono ⊢
    exact mul_le_mul_of_nonneg_left hmono (by linarith only [hs])
  have hbase : (3:ℝ) ≤ s*Real.sqrt s := by nlinarith only [mul_le_mul_of_nonneg_left hroot (by linarith only [hs] : 0 ≤ s),hs]
  have he : Real.exp (-1200*u*Real.sqrt u) ≤ Real.exp (-1200*s*Real.sqrt s)*Real.exp (-7200) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hprod,hbase]
  have h18 : (18:ℝ) ≤ Real.exp 7200 := by
    have hh := Real.add_one_le_exp (7200:ℝ)
    linarith only [hh]
  have hinv : Real.exp (-7200) ≤ (1/18:ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using! one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 18) h18
  have hc0 : 0 ≤ positiveOccupancyCost n := by unfold positiveOccupancyCost; positivity
  calc
    _ = 9*s^2*Real.exp (-1200*u*Real.sqrt u) := by
      change u^2*Real.exp (-1200*u*Real.sqrt u) = _
      rw [hu]
      ring
    _ ≤ 9*s^2*(Real.exp (-1200*s*Real.sqrt s)*Real.exp (-7200)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (9*Real.exp (-7200))*positiveOccupancyCost n := by
      change _ = (9*Real.exp (-7200))*(s^2*Real.exp (-1200*s*Real.sqrt s))
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith only [hinv]) hc0

/-- The first omitted term already pays the complete future tail allowance. -/
theorem positive_occupancy_cost_start (M : ℕ) :
    18*positiveOccupancyCost M ≤ Real.exp (-(3:ℝ)^M) := by
  let N : ℝ := (3:ℝ)^M
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hs : positiveLabelSide M = 3*N := by unfold positiveLabelSide N; rw [pow_succ]; ring
  have hroot : (1:ℝ) ≤ Real.sqrt (positiveLabelSide M) :=
    (Real.le_sqrt (by norm_num) (by linarith only [positive_label_side_ge_three M])).mpr
      (by nlinarith only [positive_label_side_ge_three M])
  have he : Real.exp (-1200*positiveLabelSide M*Real.sqrt (positiveLabelSide M)) ≤
      Real.exp (-3600*N) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ positiveLabelSide M by rw [hs]; positivity)
    nlinarith only [hm,hs]
  have ht := Real.pow_div_factorial_le_exp (3599*N) (by positivity) 2
  norm_num only [Nat.factorial,Nat.cast_ofNat] at ht
  have hp : 162*N^2 ≤ Real.exp (3599*N) := by
    have hn := sq_nonneg N
    nlinarith only [ht,hn]
  calc
    _ ≤ 162*N^2*Real.exp (-3600*N) := by
      unfold positiveOccupancyCost
      have hm := mul_le_mul_of_nonneg_left he
        (show 0 ≤ 18*(positiveLabelSide M)^2 by positivity)
      convert hm using 1
      · ring
      · rw [hs]
        ring
    _ ≤ Real.exp (3599*N)*Real.exp (-3600*N) := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (-N) := by rw [← Real.exp_add]; congr 1; ring

/-- Every omitted label and every raw site are summed: nine possible aligned
cubes per label cost at most exp(-N), N=3^M. -/
theorem omitted_positive_cost_sum (M : ℕ) :
    9*(∑' k : ℕ, positiveOccupancyCost (M+k)) ≤ Real.exp (-(3:ℝ)^M) := by
  have hb (k : ℕ) : positiveOccupancyCost (M+k) ≤ positiveOccupancyCost M*(1/2:ℝ)^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hh := (positive_occupancy_cost_succ (M+k)).trans (mul_le_mul_of_nonneg_left ih (by norm_num))
      simpa only [Nat.add_assoc,pow_succ,mul_left_comm,mul_comm,mul_assoc] using! hh
  have hg := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_left (positiveOccupancyCost M)
  have hs := hg.summable.of_nonneg_of_le (fun k => by unfold positiveOccupancyCost; positivity) hb
  have ht := hs.tsum_le_tsum hb hg.summable
  rw [hg.tsum_eq] at ht
  norm_num only at ht
  have hh := positive_occupancy_cost_start M
  nlinarith only [ht,hh]

end
end ASDExplicitGamma.Inverse
