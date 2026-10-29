module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Sharp scalar algebra for the same-law cold graph candidates -/

@[expose] public section
namespace ASDExplicitGamma.Cold

/-- The half-floor deterministic term allows unequal expected blocks. -/
theorem cold_graph_half_bias {p q r s : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrp : r ≤ p) (hsq : s ≤ q) :
    2*(p-q)*(r-s)+4*p*q ≤ (2*(p+q))^2/2 := by
  by_cases h : p ≤ q
  · have h1 := mul_nonneg (sub_nonneg.mpr h) hr
    have h2 := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hsq)
    have h3 := mul_nonneg hp (add_nonneg hp hq)
    nlinarith only [h1,h2,h3]
  · have h := le_of_not_ge h
    have h1 := mul_nonneg (sub_nonneg.mpr h) hs
    have h2 := mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr hrp)
    have h3 := mul_nonneg hq (add_nonneg hp hq)
    nlinarith only [h1,h2,h3]

/-- The favorable negative-bias term in the two-block five-sixths argument. -/
theorem cold_graph_cross_bias {p q r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    -2*(p^2+q^2)+4*(p*r+q*s) ≤
      (-(2*(p+q))^2+2*(2*(p+q))*(2*(r+s))+(2*(r+s))^2)/4 := by
  have h := mul_nonneg hr hs
  nlinarith only [sq_nonneg ((p-q)-(r-s)),h]

theorem cold_graph_fiveSixths_max (a b : ℝ) :
    (3*a^2+2*a*b-3*b^2)/4 ≤ (5/6:ℝ)*a^2 := by
  have h := sq_nonneg (a-3*b)
  nlinarith only [h]

/-- Retaining the parent trace saves its square without a covariance assumption. -/
theorem cold_graph_trace_gap_square {T Y : ℝ} (hT : 0 ≤ T) (hTY : T ≤ Y) :
    (Y-T)^2 ≤ Y^2-T^2 := by
  have h := mul_nonneg hT (sub_nonneg.mpr hTY)
  nlinarith only [h]

/-- Solve the exact quadratic produced by the two-sided response sandwich. -/
theorem cold_graph_sandwich_quadratic {z e a : ℝ}
    (h : z^2 ≤ a^2/2+2*e*z+e^2) :
    z ≤ e+Real.sqrt (a^2/2+2*e^2) := by
  have hs : (Real.sqrt (a^2/2+2*e^2))^2 = a^2/2+2*e^2 := Real.sq_sqrt (by positivity)
  have hn := Real.sqrt_nonneg (a^2/2+2*e^2)
  nlinarith only [h,hs,hn]

end ASDExplicitGamma.Cold
