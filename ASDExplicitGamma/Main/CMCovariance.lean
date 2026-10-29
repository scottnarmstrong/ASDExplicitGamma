module

public import ASDExplicitGamma.Main.CMW2

/-! Actual coefficient-direction covariance and derivative traces by Parseval. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Gaussian MeasureTheory
open scoped RealInnerProductSpace

/-- The actual covariance factor gives every mixed coordinate covariance,
including all derivative-coordinate pairs, with absolute summability. -/
theorem main_q3_direction_covariance {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (a c : H3Index) (x y : Vec 2) :
    HasSum (fun j => q3Convolution b L a (e j) x * q3Convolution b L c (e j) y)
      ⟪q3Section b L a x, q3Section b L c y⟫ := by
  have h := e.hasSum_inner_mul_inner (q3Section b L a x) (q3Section b L c y)
  convert h using 1
  funext j
  exact congrArg (fun r : ℝ => r * ⟪e j, q3Section b L c y⟫)
    (real_inner_comm (e j) (q3Section b L a x)).symm

/-- Exact square sum of an actual derivative coordinate. -/
theorem main_q3_direction_variance {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index) (x : Vec 2) :
    (∑' j, (q3Convolution b L a (e j) x)^2) =
      (b/L.1^(1+a.1.1.val+a.1.2.val))^2 *
        (L.1*q3DerivativeMoment a.1.1)*(L.1*q3DerivativeMoment a.1.2) := by
  have h := (main_q3_direction_covariance e b L a a x x).tsum_eq
  rw [real_inner_self_eq_norm_sq, gaussQ3Section_norm_sq] at h
  simpa only [pow_two] using h

/-- The first spatial derivative trace is the literal source 31.2 b²/L². -/
theorem main_q3_first_derivative_trace {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    (∑ i : Fin 2, ∑' j, ((fderiv ℝ (q3Convolution b L h3Zero (e j)) x) (basisVec i))^2) =
      (156/5)*b^2/L.1^2 := by
  have hz : h3Zero.1.1.val+h3Zero.1.2.val ≤ 2 := by decide
  simp_rw [q3Convolution_fderiv_basis b L h3Zero hz, main_q3_direction_variance]
  norm_num [Fin.sum_univ_two, h3Next, h3Zero, q3DerivativeMoment]
  field_simp
  ring

/-- The true second derivative is the successor of the true first derivative. -/
theorem main_q3_second_coordinate (b : ℝ) (L : {l : ℝ // 0 < l})
    (u : WhiteNoise) (x : Vec 2) (i j : Fin 2) :
    let hz : h3Zero.1.1.val+h3Zero.1.2.val ≤ 2 := by decide
    let ha : (h3Next h3Zero i hz).1.1.val+(h3Next h3Zero i hz).1.2.val ≤ 2 := by
      fin_cases i <;> norm_num [h3Next, h3Zero]
    (fderiv ℝ (fun y => (fderiv ℝ (q3Convolution b L h3Zero u) y) (basisVec i)) x) (basisVec j) =
      q3Convolution b L (h3Next (h3Next h3Zero i hz) j ha) u x := by
  intro hz ha
  have heq : (fun y => (fderiv ℝ (q3Convolution b L h3Zero u) y) (basisVec i)) =
      q3Convolution b L (h3Next h3Zero i hz) u :=
    funext fun y => q3Convolution_fderiv_basis b L h3Zero hz u y i
  rw [heq]
  exact q3Convolution_fderiv_basis b L _ ha u x j

/-- The actual full spatial Hessian covariance trace is 1859.52 b²/L⁴,
with both mixed entries counted in Frobenius normalization. -/
theorem main_q3_second_derivative_trace {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    (∑ i : Fin 2, ∑ k : Fin 2, ∑' j,
      ((fderiv ℝ (fun y => (fderiv ℝ (q3Convolution b L h3Zero (e j)) y)
        (basisVec i)) x) (basisVec k))^2) = (46488/25)*b^2/L.1^4 := by
  simp_rw [main_q3_second_coordinate, main_q3_direction_variance]
  norm_num [Fin.sum_univ_two, h3Next, h3Zero, q3DerivativeMoment]
  field_simp
  ring

end ASDExplicitGamma.Main
