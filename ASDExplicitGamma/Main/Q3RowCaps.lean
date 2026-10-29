module

public import ASDExplicitGamma.Main.Q3W2Jets

/-! Pointwise sharp q3 covariance row caps for genuine finite W^{2,∞} combinations. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators

/-- The value cap of an actual finite q3 row combination. -/
theorem main_q3_row_value_cap {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (s : Finset ι) (c : ι → ℝ) (x : Vec 2) :
    |(PlanarW2Infinity.linearCombination (fun j => mainQ3DirectionW2 Q b L (e j)) s c).value.toFun x| ≤
      Real.sqrt (b^2)*Real.sqrt (∑ j ∈ s, c j^2) := by
  have hg := mainQ3DirectionW2_jet_covariance e Q b L .value .value x
  have hs : Summable (fun j => (mainQ3DirectionW2 Q b L (e j)).value.toFun x^2) := by
    simpa only [q3DirectionJet, pow_two] using hg.summable
  have he : (∑' j, (mainQ3DirectionW2 Q b L (e j)).value.toFun x^2) = b^2 := by
    simpa only [q3DirectionJet, pow_two, q3ScaledJetCovariance_value_diagonal] using hg.tsum_eq
  have hb := finite_coefficient_sq_le_tsum s c
    (fun j => (mainQ3DirectionW2 Q b L (e j)).value.toFun x) hs
  rw [he] at hb
  have hr := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg (c j))] at hr
  simpa only [PlanarW2Infinity.linearCombination, h1_finset_sum_toFun, mul_comm] using hr

/-- Sharp gradient ROW cap, with 15.6 rather than the Hilbert--Schmidt trace. -/
theorem main_q3_row_gradient_cap {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (s : Finset ι) (c : ι → ℝ) (x : Vec 2) :
    planarEuclideanNorm (planarW1Value
      (PlanarW2Infinity.linearCombination (fun j => mainQ3DirectionW2 Q b L (e j)) s c).gradient x) ≤
      Real.sqrt ((78/5)*b^2/L.1^2)*Real.sqrt (∑ j ∈ s, c j^2) := by
  have hb := main_q3_first_row_bound e s c b L x
  have hr := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul (by positivity : 0 ≤ (78/5:ℝ)*b^2/L.1^2)] at hr
  have he (j : ι) (i : Fin 2) :
      ((mainQ3DirectionW2 Q b L (e j)).gradient.component i).toFun x =
        q3Convolution b L (mainQ3JetIndex (.first i)) (e j) x :=
    (congrFun ((mainQ3DirectionW2 Q b L (e j)).gradient_eq i) x).trans
      (mainQ3DirectionW2_jet Q b L (e j) (.first i) x)
  simpa only [planarEuclideanNorm, planarW1Value, PlanarW2Infinity.linearCombination,
    PlanarW1Infinity.linearCombination, h1_finset_sum_toFun, he] using hr

/-- Sharp Hessian ROW cap, retaining the full covariance operator quadratic form. -/
theorem main_q3_row_hessian_cap {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (s : Finset ι) (c : ι → ℝ) (x : Vec 2) :
    planarFrobeniusNorm (planarW1Derivative
      (PlanarW2Infinity.linearCombination (fun j => mainQ3DirectionW2 Q b L (e j)) s c).gradient x) ≤
      Real.sqrt ((23244/25)*b^2/L.1^4)*Real.sqrt (∑ j ∈ s, c j^2) := by
  have hb := main_q3_second_row_bound e s c b L x
  have hr := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul (by positivity : 0 ≤ (23244/25:ℝ)*b^2/L.1^4)] at hr
  have he (j : ι) (i k : Fin 2) :
      ((mainQ3DirectionW2 Q b L (e j)).gradient.component i).grad x k =
        q3Convolution b L (mainQ3JetIndex (.second i k)) (e j) x :=
    mainQ3DirectionW2_jet Q b L (e j) (.second i k) x
  simpa only [planarFrobeniusNorm, planarW1Derivative, PlanarW2Infinity.linearCombination,
    PlanarW1Infinity.linearCombination, h1_finset_sum_grad_apply, he,
    Fintype.sum_prod_type] using hr

end ASDExplicitGamma.Main
