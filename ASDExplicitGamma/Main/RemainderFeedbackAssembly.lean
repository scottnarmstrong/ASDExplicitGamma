module

public import ASDExplicitGamma.Main.ErrorCoefficients

/-! Scalar assembly of the two positive-split remainder-feedback rows. -/

@[expose] public section

namespace ASDExplicitGamma.Main

/-- The global-bank and mixed-bridge rows imply the exact remainder-feedback
term in `mainError`. The two moment inequalities are kept as separate
producer outputs; the proof only combines them with the nonnegative source
coefficient. -/
theorem main_remainder_feedback_bound_of_source_rows
    (v a f H xi bdMoment bgdMoment : ℝ)
    (hBd : bdMoment ≤ mainBeta * mainLoadD v a f H xi (mainKd v))
    (hBGd : bgdMoment ≤ mainLoadZ v a f H xi (mainKd v) * mainRec xi) :
    2 * mainKd v * (63 / 50) *
        (Real.sqrt 2 * bdMoment + bgdMoment) ≤
      2 * mainKd v * (63 / 50) *
        (Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) +
          mainLoadZ v a f H xi (mainKd v) * mainRec xi) := by
  have hInner : Real.sqrt 2 * bdMoment + bgdMoment ≤
      Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) +
        mainLoadZ v a f H xi (mainKd v) * mainRec xi := by
    have hsqrt : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
    have hFirst : Real.sqrt 2 * bdMoment ≤
        Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) := by
      calc
        Real.sqrt 2 * bdMoment ≤
            Real.sqrt 2 * (mainBeta * mainLoadD v a f H xi (mainKd v)) :=
          mul_le_mul_of_nonneg_left hBd hsqrt
        _ = Real.sqrt 2 * mainBeta * mainLoadD v a f H xi (mainKd v) := by ring
    exact add_le_add hFirst hBGd
  have hkd : 0 ≤ mainKd v := mainKd_nonneg v
  have hCoefficient : 0 ≤ 2 * mainKd v * (63 / 50) := by
    positivity
  exact mul_le_mul_of_nonneg_left hInner hCoefficient

end ASDExplicitGamma.Main
