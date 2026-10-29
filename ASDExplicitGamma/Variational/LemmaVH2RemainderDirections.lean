module

public import ASDExplicitGamma.Variational.LemmaVH2RemainderKernel

/-! Caps for the actual common-center remainder direction family. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

 theorem q3Remainder_direction_value_cap {Q : TriadicCube 2}
    (η : ℕ → PlanarW2Infinity Q) (v L : ℝ)
    (hrep : RepresentsQ3Remainder η v L (cubeCenter Q)) (hv : 0 ≤ v)
    (t : Finset ℕ) (c : ℕ → ℝ) {x : Vec 2} (hx : x ∈ cubeSet Q) :
    |(PlanarW2Infinity.linearCombination η t c).value.toFun x| ≤
      Real.sqrt (v*(lemmaVH2R1/2)*(cubeScaleFactor Q/L)^2)*Real.sqrt (∑ l ∈ t, c l^2) := by
  have hg := hrep .value .value x x
  have hs : Summable (fun l => (η l).value.toFun x ^ 2) := by simpa only [q3DirectionJet, pow_two] using hg.1
  have hb := finite_coefficient_sq_le_tsum t c (fun l => (η l).value.toFun x) hs
  have he : (∑' l, (η l).value.toFun x ^ 2) = q3RemainderJetCovariance v L (cubeCenter Q) .value .value x x := by
    simpa only [q3DirectionJet, pow_two] using hg.2
  rw [he] at hb
  have hh := hb.trans (mul_le_mul_of_nonneg_left (q3RemainderJetCovariance_value_cap hv Q hx)
    (Finset.sum_nonneg fun l _ => sq_nonneg (c l)))
  have hr := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (Finset.sum_nonneg fun l _ => sq_nonneg (c l))] at hr
  simpa only [PlanarW2Infinity.linearCombination, h1_finset_sum_toFun, mul_comm] using hr

 theorem q3Remainder_direction_gradient_cap {Q : TriadicCube 2}
    (η : ℕ → PlanarW2Infinity Q) (v L : ℝ) (z : Vec 2)
    (hrep : RepresentsQ3Remainder η v L z) (hv : 0 ≤ v)
    (t : Finset ℕ) (c : ℕ → ℝ) (x : Vec 2) :
    planarEuclideanNorm (planarW1Value (PlanarW2Infinity.linearCombination η t c).gradient x) ≤
      Real.sqrt (lemmaVH2R1*(v/L^2))*Real.sqrt (∑ l ∈ t, c l^2) := by
  have hM : 0 ≤ (78/5:ℝ)*(v/L^2) := mul_nonneg (by norm_num) (div_nonneg hv (sq_nonneg L))
  have hb := finite_vector_coefficient_sq_bound
    (fun l i => q3DirectionJet (η l) (.first i) x)
    (fun i j => q3ScaledJetCovariance v L (.first i) (.first j) x x)
    (fun i j => (hrep (.first i) (.first j) x x).1)
    (fun i j => (hrep (.first i) (.first j) x x).2) hM
    (fun a => (q3ScaledJetCovariance_first_quadratic v L x a).le) t c
  have hr := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul hM] at hr
  simpa only [planarEuclideanNorm, planarW1Value, PlanarW2Infinity.linearCombination,
    PlanarW1Infinity.linearCombination, h1_finset_sum_toFun, q3DirectionJet,
    PlanarW2Infinity.gradient_eq, lemmaVH2R1] using hr

 theorem q3Remainder_direction_hessian_cap {Q : TriadicCube 2}
    (η : ℕ → PlanarW2Infinity Q) (v L : ℝ) (z : Vec 2)
    (hrep : RepresentsQ3Remainder η v L z) (hv : 0 ≤ v) (hL : 0 < L)
    (t : Finset ℕ) (c : ℕ → ℝ) (x : Vec 2) :
    planarFrobeniusNorm (planarW1Derivative (PlanarW2Infinity.linearCombination η t c).gradient x) ≤
      Real.sqrt (lemmaVH2A2*(v/L^4))*Real.sqrt (∑ l ∈ t, c l^2) := by
  have hM : 0 ≤ ((3432/5:ℝ)+(78/5:ℝ)^2)*(v/L^4) :=
    mul_nonneg (by norm_num) (div_nonneg hv (pow_nonneg hL.le 4))
  have hb := finite_vector_coefficient_sq_bound
    (fun l (i : Fin 2 × Fin 2) => q3DirectionJet (η l) (.second i.1 i.2) x)
    (fun (i j : Fin 2 × Fin 2) => q3ScaledJetCovariance v L (.second i.1 i.2) (.second j.1 j.2) x x)
    (fun i j => (hrep (.second i.1 i.2) (.second j.1 j.2) x x).1)
    (fun i j => (hrep (.second i.1 i.2) (.second j.1 j.2) x x).2) hM
    (q3ScaledJetCovariance_second_quadratic_le hv L x) t c
  have hr := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul hM] at hr
  simpa only [planarFrobeniusNorm, planarW1Derivative, PlanarW2Infinity.linearCombination,
    PlanarW1Infinity.linearCombination, h1_finset_sum_grad_apply, q3DirectionJet,
    Fintype.sum_prod_type, lemmaVH2A2, lemmaVH2R1] using hr

end
end ASDExplicitGamma.Variational
