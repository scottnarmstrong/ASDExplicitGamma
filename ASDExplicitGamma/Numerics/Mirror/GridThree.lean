module

public import ASDExplicitGamma.Numerics.Mirror.GridExp
import Mathlib.Tactic.NormNum

/-!
# The constant `log 3` and powers of three

The logarithm needed by the certificate formulas is enclosed by the already proved rational
`log 3` bracket. A general interval logarithm is not needed for this operation.
-/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Mirror

open ASDExplicitGamma.Numerics

/-- The rational endpoints in the 30-decimal enclosure of `log 3`. -/
def logThreeRaw : QInterval :=
  ⟨1.098612288668109691395245236922,
    1.098612288668109691395245236923, by norm_num⟩

theorem logThreeRaw_sound : QInterval.Contains logThreeRaw (Real.log 3) := by
  change (1.098612288668109691395245236922 : ℝ) ≤ Real.log 3 ∧
    Real.log 3 ≤ 1.098612288668109691395245236923
  exact log_three_enclosure_30

/-- The `log 3` enclosure rounded outward to the requested grid. -/
def logThree (G : ℕ) : QInterval := round G logThreeRaw

theorem logThree_sound (G : ℕ) : QInterval.Contains (logThree G) (Real.log 3) :=
  round_contains G logThreeRaw_sound

/-- Grid-rounded `3^x`, using `exp (x * log 3)`. -/
def powThree (G n : ℕ) (a : QInterval) (hn : 5 ≤ n)
    (hlo : -50 ≤ (mul G a (logThree G)).lo)
    (hhi : (mul G a (logThree G)).hi ≤ 50) : QInterval :=
  exp G n (mul G a (logThree G)) hn hlo hhi

theorem powThree_sound (G n : ℕ) {a : QInterval} {x : ℝ} (hn : 5 ≤ n)
    (hlo : -50 ≤ (mul G a (logThree G)).lo)
    (hhi : (mul G a (logThree G)).hi ≤ 50)
    (hx : QInterval.Contains a x) :
    QInterval.Contains (powThree G n a hn hlo hhi) ((3 : ℝ) ^ x) := by
  have harg := mul_sound G hx (logThree_sound G)
  have hexp := exp_sound G n hn hlo hhi harg
  have hpow : (3 : ℝ) ^ x = Real.exp (x * Real.log 3) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  simpa [powThree, hpow] using hexp

end ASDExplicitGamma.Numerics.Mirror
