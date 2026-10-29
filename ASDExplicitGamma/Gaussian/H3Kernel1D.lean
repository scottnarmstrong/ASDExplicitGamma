module

public import ASDExplicitGamma.Model.Q3Moments
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section

open MeasureTheory Set Filter ASDExplicitGamma.Model
open scoped Topology

namespace ASDExplicitGamma.Gaussian

noncomputable def q3SecondPolynomial (x : ℝ) : ℝ :=
  Real.sqrt (3003 / 1024) * (-24 + 576 * x ^ 2 - 1920 * x ^ 4)

noncomputable def q3ThirdPolynomial (x : ℝ) : ℝ :=
  Real.sqrt (3003 / 1024) * (1152 * x - 7680 * x ^ 3)

theorem q3SecondPolynomial_hasDerivAt (x : ℝ) :
    HasDerivAt q3SecondPolynomial (q3ThirdPolynomial x) x := by
  convert (((hasDerivAt_const x (-24 : ℝ)).add
    ((hasDerivAt_pow 2 x).const_mul 576)).sub
      ((hasDerivAt_pow 4 x).const_mul 1920)).const_mul (Real.sqrt (3003 / 1024)) using 1
  all_goals first
    | rfl
    | (dsimp [q3SecondPolynomial, q3ThirdPolynomial]; ring)

theorem q3Second_eq_indicator :
    q3KernelD2 = (Icc (-(1 / 2 : ℝ)) (1 / 2)).indicator q3SecondPolynomial := by
  funext x
  by_cases hx : |x| ≤ 1 / 2
  · have hp : 0 ≤ 1 - 4 * x ^ 2 := by nlinarith [abs_le.mp hx |>.1, abs_le.mp hx |>.2]
    rw [indicator_of_mem (by simpa only [mem_Icc, abs_le] using hx)]
    simp only [q3KernelD2, max_eq_left hp, q3SecondPolynomial]
    ring
  · have hp : 1 - 4 * x ^ 2 ≤ 0 := by nlinarith [lt_of_not_ge hx, sq_abs x]
    rw [indicator_of_notMem (by simpa only [mem_Icc, abs_le] using hx)]
    simp only [q3KernelD2, max_eq_right hp]
    ring

theorem q3Third_eq_indicator :
    q3KernelD3 = (Ioo (-(1 / 2 : ℝ)) (1 / 2)).indicator q3ThirdPolynomial := by
  funext x
  simp only [q3KernelD3, indicator, mem_Ioo, ← abs_lt, q3ThirdPolynomial]

end ASDExplicitGamma.Gaussian
