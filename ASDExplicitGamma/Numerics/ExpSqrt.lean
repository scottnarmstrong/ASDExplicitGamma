module

public import ASDExplicitGamma.Numerics.Enclosures
import Mathlib.Tactic.NormNum

/-!
# Rational exponential and square-root brackets

The executable parts of these bounds use rational polynomials and integer
square comparisons. Analytic soundness is proved in the kernel.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics

/-- Rational Taylor polynomial for the exponential. -/
def expPolyQ (q : ℚ) (n : ℕ) : ℚ :=
  ∑ m ∈ Finset.range n, q ^ m / m.factorial

/-- Rational Taylor remainder bound for the exponential. -/
def expErrQ (q : ℚ) (n : ℕ) : ℚ :=
  |q| ^ n * ((n.succ : ℚ) / (n.factorial * n))

theorem expPolyQ_cast (q : ℚ) (n : ℕ) :
    (expPolyQ q n : ℝ) = expPoly (q : ℝ) n := by
  simp [expPolyQ, expPoly]

theorem expErrQ_cast (q : ℚ) (n : ℕ) :
    (expErrQ q n : ℝ) = expErr (q : ℝ) n := by
  simp [expErrQ, expErr]

/-- Rational form of the Taylor enclosure on `[-1,1]`. -/
theorem exp_enclosure_rat {q : ℚ} (hq : |(q : ℝ)| ≤ 1) {n : ℕ} (hn : 0 < n) :
    (expPolyQ q n : ℝ) - expErrQ q n ≤ Real.exp q ∧
      Real.exp q ≤ (expPolyQ q n : ℝ) + expErrQ q n := by
  simpa [expPolyQ_cast, expErrQ_cast] using exp_enclosure hq hn

/-- Exponential enclosure for an arbitrary rational argument by scaling it into `[-1,1]`.
The supplied rational endpoints enclose the Taylor polynomial and remainder at `q / m`. -/
theorem exp_enclosure_rat_scaled {q lo hi : ℚ} {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hq : |((q : ℝ) / m)| ≤ 1) (hlo0 : 0 ≤ lo)
    (hlo : (lo : ℝ) ≤ (expPolyQ (q / m) n : ℝ) - expErrQ (q / m) n)
    (hhi : (expPolyQ (q / m) n : ℝ) + expErrQ (q / m) n ≤ hi) :
    (lo : ℝ) ^ m ≤ Real.exp q ∧ Real.exp q ≤ (hi : ℝ) ^ m := by
  have hqdiv : ((q / m : ℚ) : ℝ) = (q : ℝ) / m := by norm_num
  have hq' : |((q / m : ℚ) : ℝ)| ≤ 1 := by rw [hqdiv]; exact hq
  have hsmall := exp_enclosure_rat (q := q / m) hq' hn
  have hlo' : (lo : ℝ) ≤ Real.exp ((q : ℝ) / m) := by
    rw [← hqdiv]
    exact le_trans hlo hsmall.1
  have hhi' : Real.exp ((q : ℝ) / m) ≤ (hi : ℝ) := by
    rw [← hqdiv]
    exact le_trans hsmall.2 hhi
  exact exp_bounds_of_div hm (by exact_mod_cast hlo0) hlo' hhi'

/-- Square-root enclosure from nonnegative rational square brackets. -/
theorem sqrt_enclosure_rat {x lo hi : ℚ} (hlo0 : 0 ≤ lo) (hhi0 : 0 ≤ hi)
    (hlo : lo ^ 2 ≤ x) (hhi : x ≤ hi ^ 2) :
    (lo : ℝ) ≤ Real.sqrt x ∧ Real.sqrt x ≤ hi := by
  have hlo0R : (0 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo0
  have hlow : (lo : ℝ) ≤ Real.sqrt x := by
    rw [← abs_of_nonneg hlo0R]
    exact Real.le_sqrt_of_sq_le (by simpa [sq_abs] using (show (lo : ℝ) ^ 2 ≤ x by exact_mod_cast hlo))
  exact ⟨hlow, Real.sqrt_le_iff.2 ⟨by exact_mod_cast hhi0, by exact_mod_cast hhi⟩⟩

end ASDExplicitGamma.Numerics
