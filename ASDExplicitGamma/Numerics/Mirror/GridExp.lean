module

public import ASDExplicitGamma.Numerics.Mirror.GridInterval
public import ASDExplicitGamma.Numerics.ExpSqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Computed grid enclosures for the exponential

Arguments in `[-50,50]` are divided by 50, enclosed with the rational Taylor polynomial and
the certified remainder from `ExpSqrt`, and raised back to the fiftieth power. The Taylor
degree is an input and must be at least five.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Mirror

open ASDExplicitGamma.Numerics

/-- A rational Taylor remainder is uniformly small on `[-1,1]` for degree at least five. -/
theorem expErrQ_le_one_twelfth {r : ℚ} {n : ℕ} (hr : |r| ≤ 1) (hn : 5 ≤ n) :
    expErrQ r n ≤ 1 / 12 := by
  have hpow : |r| ^ n ≤ (1 : ℚ) := pow_le_one₀ (abs_nonneg r) hr
  have hfac : 120 ≤ n.factorial := by
    calc
      120 = (5 : ℕ).factorial := by norm_num
      _ ≤ n.factorial := Nat.factorial_le hn
  have hn1 : n + 1 ≤ 10 * n := by nlinarith
  have hcoeffNat : 12 * (n + 1) ≤ n.factorial * n := by
    calc
      12 * (n + 1) ≤ 12 * (10 * n) := Nat.mul_le_mul_left 12 hn1
      _ = 120 * n := by ring
      _ ≤ n.factorial * n := Nat.mul_le_mul_right n hfac
  have hcoeff : (n.succ : ℚ) / (n.factorial * n) ≤ 1 / 12 := by
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < n.factorial * n)).2
    have hcoeffQ : (n.succ : ℚ) * 12 ≤ (n.factorial : ℚ) * n := by
      rw [Nat.succ_eq_add_one]
      have hcoeffNat' : (n + 1) * 12 ≤ n.factorial * n := by
        simpa [Nat.mul_comm] using hcoeffNat
      exact_mod_cast hcoeffNat'
    nlinarith
  rw [expErrQ]
  calc
    |r| ^ n * ((n.succ : ℚ) / (n.factorial * n)) ≤
        1 * ((n.succ : ℚ) / (n.factorial * n)) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ ≤ 1 / 12 := by simpa using hcoeff

/-- The Taylor lower bracket at `-1`, with six terms, exceeds `1/3`. -/
theorem one_third_le_exp_neg_one : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
  have hTaylor := exp_enclosure_rat (q := (-1 : ℚ)) (by norm_num) (by norm_num : 0 < 6)
  have hnum : (1 / 3 : ℝ) ≤
      (expPolyQ (-1) 6 : ℝ) - expErrQ (-1) 6 := by
    norm_num [expPolyQ, expErrQ, Finset.sum_range_succ, Nat.factorial]
  simpa using hnum.trans hTaylor.1

/-- The degree-`n` Taylor lower endpoint on `[-1,1]` is positive for `n ≥ 5`. -/
theorem expTaylorLower_nonneg {r : ℚ} {n : ℕ} (hr : -1 ≤ r ∧ r ≤ 1)
    (hn : 5 ≤ n) : 0 ≤ expPolyQ r n - expErrQ r n := by
  have hrAbsQ : |r| ≤ (1 : ℚ) := abs_le.mpr hr
  have hrAbs : |(r : ℝ)| ≤ 1 := by exact_mod_cast hrAbsQ
  have hTaylor := exp_enclosure_rat hrAbs (lt_of_lt_of_le (by norm_num : 0 < 5) hn)
  have hExpLo : (1 / 3 : ℝ) ≤ Real.exp r := by
    exact one_third_le_exp_neg_one.trans
      (Real.exp_le_exp.mpr (by exact_mod_cast hr.1))
  have hErrQ := expErrQ_le_one_twelfth hrAbsQ hn
  have hErr : (expErrQ r n : ℝ) ≤ 1 / 12 := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hErrQ
  have hPolyHi : Real.exp r ≤ (expPolyQ r n : ℝ) + expErrQ r n := hTaylor.2
  have hLowerReal : (1 / 6 : ℝ) ≤ (expPolyQ r n : ℝ) - expErrQ r n := by
    linarith
  have hLowerQ : (1 / 6 : ℚ) ≤ expPolyQ r n - expErrQ r n := by
    have hLowerReal' : ((1 / 6 : ℚ) : ℝ) ≤
        ((expPolyQ r n - expErrQ r n : ℚ) : ℝ) := by simpa using hLowerReal
    exact_mod_cast hLowerReal'
  linarith

/-- The reduced argument `q/50` lies in `[-1,1]` when `q` lies in `[-50,50]`. -/
theorem expReduced_mem {q : ℚ} (hlo : -50 ≤ q) (hhi : q ≤ 50) :
    -1 ≤ q / 50 ∧ q / 50 ≤ 1 := by
  constructor
  · apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 50)).2
    nlinarith
  · apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 50)).2
    nlinarith

/-- Computed lower grid endpoint for `exp q`, using degree-`n` Taylor after reduction. -/
def expPointLower (G n : ℕ) (q : ℚ) : ℚ :=
  roundDown G ((expPolyQ (q / 50) n - expErrQ (q / 50) n) ^ 50)

/-- Computed upper grid endpoint for `exp q`, using degree-`n` Taylor after reduction. -/
def expPointUpper (G n : ℕ) (q : ℚ) : ℚ :=
  roundUp G ((expPolyQ (q / 50) n + expErrQ (q / 50) n) ^ 50)

theorem expPoint_bounds (G n : ℕ) {q : ℚ} (hn : 5 ≤ n)
    (hlo : -50 ≤ q) (hhi : q ≤ 50) :
    (expPointLower G n q : ℝ) ≤ Real.exp q ∧
      Real.exp q ≤ expPointUpper G n q := by
  have hr := expReduced_mem hlo hhi
  have hrAbsQ : |q / 50| ≤ (1 : ℚ) := abs_le.mpr hr
  have hrAbs : |((q : ℝ) / 50)| ≤ 1 := by
    have hcast : ((q / 50 : ℚ) : ℝ) = (q : ℝ) / 50 := by norm_num
    rw [← hcast]
    exact_mod_cast hrAbsQ
  have hredLo : 0 ≤ expPolyQ (q / 50) n - expErrQ (q / 50) n :=
    expTaylorLower_nonneg hr hn
  have hscaled := exp_enclosure_rat_scaled (q := q)
    (lo := expPolyQ (q / 50) n - expErrQ (q / 50) n)
    (hi := expPolyQ (q / 50) n + expErrQ (q / 50) n)
    (m := 50) (n := n) (by norm_num) (lt_of_lt_of_le (by norm_num : 0 < 5) hn) hrAbs
    (by exact_mod_cast hredLo) (by norm_num) (by norm_num)
  constructor
  · have hround : (roundDown G
        ((expPolyQ (q / 50) n - expErrQ (q / 50) n) ^ 50) : ℝ) ≤
        ((expPolyQ (q / 50) n - expErrQ (q / 50) n : ℚ) : ℝ) ^ 50 := by
      exact_mod_cast roundDown_le G _
    exact hround.trans hscaled.1
  · have hround : ((expPolyQ (q / 50) n + expErrQ (q / 50) n : ℚ) : ℝ) ^ 50 ≤
        (roundUp G
          ((expPolyQ (q / 50) n + expErrQ (q / 50) n) ^ 50) : ℝ) := by
      exact_mod_cast le_roundUp G _
    exact hscaled.2.trans hround

/-- Grid-rounded exponential on an interval whose endpoints lie in `[-50,50]`. -/
def exp (G n : ℕ) (a : QInterval) (hn : 5 ≤ n)
    (hlo : -50 ≤ a.lo) (hhi : a.hi ≤ 50) : QInterval :=
  ⟨expPointLower G n a.lo, expPointUpper G n a.hi,
    by
      have hleft := (expPoint_bounds G n hn hlo (a.valid.trans hhi)).1
      have hright := (expPoint_bounds G n hn (hlo.trans a.valid) hhi).2
      have hmono : Real.exp (a.lo : ℝ) ≤ Real.exp a.hi :=
        Real.exp_le_exp.mpr (by exact_mod_cast a.valid)
      exact_mod_cast hleft.trans (hmono.trans hright)⟩

theorem exp_sound (G n : ℕ) {a : QInterval} {x : ℝ} (hn : 5 ≤ n)
    (hlo : -50 ≤ a.lo) (hhi : a.hi ≤ 50) (hx : QInterval.Contains a x) :
    QInterval.Contains (exp G n a hn hlo hhi) (Real.exp x) := by
  change (a.lo : ℝ) ≤ x ∧ x ≤ a.hi at hx
  have hleft := (expPoint_bounds G n hn hlo (a.valid.trans hhi)).1
  have hright := (expPoint_bounds G n hn (hlo.trans a.valid) hhi).2
  exact ⟨hleft.trans (Real.exp_le_exp.mpr hx.1),
    (Real.exp_le_exp.mpr hx.2).trans hright⟩

end ASDExplicitGamma.Numerics.Mirror
