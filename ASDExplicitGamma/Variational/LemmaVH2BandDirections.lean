module

public import ASDExplicitGamma.Model.Q3DerivativeBand
public import ASDExplicitGamma.Triadic.FiniteGramBounds
public import ASDExplicitGamma.Triadic.PlanarDirectionLinear
public import ASDExplicitGamma.Variational.LemmaVH2Constants

/-! A given Gaussian representation is identified by all actual covariance Gram rows.
No value, derivative, product, or interpolant estimate is part of this predicate. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

 def q3DirectionJet {Q : TriadicCube 2} (η : PlanarW2Infinity Q) : Q3SpatialJet → Vec 2 → ℝ
  | .value, x => η.value.toFun x
  | .first i, x => η.value.grad x i
  | .second i j, x => (η.gradient.component i).grad x j

/-- Exact representation semantics, including cross-point and cross-jet rows.
The shell variances are already divided by the square of the physical frame. -/
def RepresentsQ3Band {Q : TriadicCube 2} {ι : Type*} (η : ℕ → PlanarW2Infinity Q)
    (s : Finset ι) (v L : ι → ℝ) : Prop :=
  ∀ (o p : Q3SpatialJet) (x y : Vec 2),
    Summable (fun l => q3DirectionJet (η l) o x*q3DirectionJet (η l) p y) ∧
    (∑' l, q3DirectionJet (η l) o x*q3DirectionJet (η l) p y) =
      q3BandJetCovariance s v L o p x y

 theorem q3Band_direction_value_cap {Q : TriadicCube 2} {ι : Type*}
    (η : ℕ → PlanarW2Infinity Q) (s : Finset ι) (v L : ι → ℝ)
    (hrep : RepresentsQ3Band η s v L)
    (t : Finset ℕ) (c : ℕ → ℝ) (x : Vec 2) :
    |(PlanarW2Infinity.linearCombination η t c).value.toFun x| ≤
      Real.sqrt (q3BandMoment s v L 0)*Real.sqrt (∑ l ∈ t, c l^2) := by
  have hg := hrep .value .value x x
  have hs : Summable (fun l => (η l).value.toFun x ^ 2) := by simpa only [q3DirectionJet, pow_two] using hg.1
  have he : (∑' l, (η l).value.toFun x ^ 2) = q3BandMoment s v L 0 := by
    simpa only [q3DirectionJet, pow_two, q3BandJetCovariance_value_diagonal] using hg.2
  have hb := finite_coefficient_sq_le_tsum t c (fun l => (η l).value.toFun x) hs
  rw [he] at hb
  have hr := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (Finset.sum_nonneg fun l _ => sq_nonneg (c l))] at hr
  simpa only [PlanarW2Infinity.linearCombination, h1_finset_sum_toFun, mul_comm] using hr

 theorem q3Band_direction_gradient_cap {Q : TriadicCube 2} {ι : Type*}
    (η : ℕ → PlanarW2Infinity Q) (s : Finset ι) (v L : ι → ℝ)
    (hrep : RepresentsQ3Band η s v L) (hv : ∀ k ∈ s, 0 ≤ v k) (hL : ∀ k ∈ s, 0 < L k)
    (t : Finset ℕ) (c : ℕ → ℝ) (x : Vec 2) :
    planarEuclideanNorm (planarW1Value (PlanarW2Infinity.linearCombination η t c).gradient x) ≤
      Real.sqrt (lemmaVH2R1*q3BandMoment s v L 2)*Real.sqrt (∑ l ∈ t, c l^2) := by
  have hM : 0 ≤ (78/5:ℝ)*q3BandMoment s v L 2 := mul_nonneg (by norm_num) (q3BandMoment_nonneg s v L 2 hv hL)
  have hb := finite_vector_coefficient_sq_bound
    (fun l i => q3DirectionJet (η l) (.first i) x)
    (fun i j => q3BandJetCovariance s v L (.first i) (.first j) x x)
    (fun i j => (hrep (.first i) (.first j) x x).1)
    (fun i j => (hrep (.first i) (.first j) x x).2) hM
    (fun a => (q3BandJetCovariance_first_quadratic s v L x a).le) t c
  have hr := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul hM] at hr
  simpa only [planarEuclideanNorm, planarW1Value, PlanarW2Infinity.linearCombination,
    PlanarW1Infinity.linearCombination, h1_finset_sum_toFun, q3DirectionJet,
    PlanarW2Infinity.gradient_eq, lemmaVH2R1] using hr

 theorem q3Band_direction_hessian_cap {Q : TriadicCube 2} {ι : Type*}
    (η : ℕ → PlanarW2Infinity Q) (s : Finset ι) (v L : ι → ℝ)
    (hrep : RepresentsQ3Band η s v L) (hv : ∀ k ∈ s, 0 ≤ v k) (hL : ∀ k ∈ s, 0 < L k)
    (t : Finset ℕ) (c : ℕ → ℝ) (x : Vec 2) :
    planarFrobeniusNorm (planarW1Derivative (PlanarW2Infinity.linearCombination η t c).gradient x) ≤
      Real.sqrt (lemmaVH2A2*q3BandMoment s v L 4)*Real.sqrt (∑ l ∈ t, c l^2) := by
  have hM : 0 ≤ ((3432/5:ℝ)+(78/5:ℝ)^2)*q3BandMoment s v L 4 :=
    mul_nonneg (by norm_num) (q3BandMoment_nonneg s v L 4 hv hL)
  have hb := finite_vector_coefficient_sq_bound
    (fun l (i : Fin 2 × Fin 2) => q3DirectionJet (η l) (.second i.1 i.2) x)
    (fun (i j : Fin 2 × Fin 2) => q3BandJetCovariance s v L (.second i.1 i.2) (.second j.1 j.2) x x)
    (fun i j => (hrep (.second i.1 i.2) (.second j.1 j.2) x x).1)
    (fun i j => (hrep (.second i.1 i.2) (.second j.1 j.2) x x).2) hM
    (q3BandJetCovariance_second_quadratic_le s v L hv x) t c
  have hr := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_mul hM] at hr
  simpa only [planarFrobeniusNorm, planarW1Derivative, PlanarW2Infinity.linearCombination,
    PlanarW1Infinity.linearCombination, h1_finset_sum_grad_apply, q3DirectionJet,
    Fintype.sum_prod_type, lemmaVH2A2, lemmaVH2R1] using hr

end
end ASDExplicitGamma.Variational
