module

public import ASDExplicitGamma.Triadic.DiagCoordinate

/-! Exact orthogonal centered bilinear moments on each physical source cell. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Independence of the two normalized cube coordinates. -/
theorem diagCoordinate_product_average (Q : TriadicCube 2) (f g : ℝ → ℝ)
    (hf : Measurable f) (hg : Measurable g) :
    cubeAverage Q (fun x => f (x 0) * g (x 1)) =
      cubeAverage Q (fun x => f (x 0)) * cubeAverage Q (fun x => g (x 1)) := by
  let L := cubeScaleFactor Q
  let μ : Fin 2 → Measure ℝ := fun k => ENNReal.ofReal L⁻¹ •
    volume.restrict (Ico (cubeCorner Q k) (cubeCorner Q k + L))
  have diagMomentsProbability (k : Fin 2) : IsProbabilityMeasure (μ k) :=
    diagInterval_probability _ (cubeScaleFactor_pos' Q)
  simp only [cubeAverage_eq_integral_normalizedCubeMeasure, ← boxMeasure_eq_normalizedCubeMeasure]
  change (∫ x, f (x 0) * g (x 1) ∂Measure.pi μ) =
    (∫ x, f (x 0) ∂Measure.pi μ) * ∫ x, g (x 1) ∂Measure.pi μ
  rw [integral_comp_eval hf.aestronglyMeasurable, integral_comp_eval hg.aestronglyMeasurable]
  have hprod := integral_fintype_prod_eq_prod (μ := μ) (fun i : Fin 2 => if i = 0 then f else g)
  simpa only [Fin.prod_univ_two, Fin.isValue, ite_true, ite_false,
    show (1 : Fin 2) ≠ 0 by decide] using hprod

/-- Mixed coordinate powers factor exactly, with normalized physical measure. -/
theorem diagCenteredCoordinate_mixed (Q : TriadicCube 2) (a b : ℕ) :
    cubeAverage Q (fun x => diagCenteredCoordinate Q 0 x ^ a * diagCenteredCoordinate Q 1 x ^ b) =
      cubeAverage Q (fun x => diagCenteredCoordinate Q 0 x ^ a) *
      cubeAverage Q (fun x => diagCenteredCoordinate Q 1 x ^ b) := by
  exact diagCoordinate_product_average Q
    (fun t => ((t-cubeCorner Q 0)/cubeScaleFactor Q-1/2)^a)
    (fun t => ((t-cubeCorner Q 1)/cubeScaleFactor Q-1/2)^b) (by fun_prop) (by fun_prop)

/-- Centered bilinear basis, ordered 1, t₀, t₁, t₀t₁. -/
def diagBilinearBasis (Q : TriadicCube 2) (a : Fin 4) (x : Vec 2) : ℝ :=
  ![1, diagCenteredCoordinate Q 0 x, diagCenteredCoordinate Q 1 x,
    diagCenteredCoordinate Q 0 x * diagCenteredCoordinate Q 1 x] a

def diagBilinearWeight (a : Fin 4) : ℝ := ![1, 1/12, 1/12, 1/144] a

theorem diagBilinearBasis_continuous (Q : TriadicCube 2) (a : Fin 4) :
    Continuous (diagBilinearBasis Q a) := by
  unfold diagBilinearBasis diagCenteredCoordinate
  fin_cases a <;> dsimp <;> fun_prop

/-- The centered basis is orthogonal, including its mixed term. -/
theorem diagBilinearBasis_pairing (Q : TriadicCube 2) (a b : Fin 4) :
    pairing Q (diagBilinearBasis Q a) (diagBilinearBasis Q b) =
      if a = b then diagBilinearWeight a else 0 := by
  have he (i : Fin 2) : cubeAverage Q (fun x => diagCenteredCoordinate Q i x ^ 2) = 1/12 :=
    by simpa only [energy, pairing, pow_two] using diagCenteredCoordinate_energy Q i
  have h11 : cubeAverage Q (fun x => diagCenteredCoordinate Q 0 x * diagCenteredCoordinate Q 1 x) = 0 := by
    simpa only [pow_one, diagCenteredCoordinate_mean, zero_mul] using diagCenteredCoordinate_mixed Q 1 1
  have h21 : cubeAverage Q (fun x => diagCenteredCoordinate Q 0 x ^ 2 * diagCenteredCoordinate Q 1 x) = 0 := by
    simpa only [pow_one, he, diagCenteredCoordinate_mean, mul_zero] using diagCenteredCoordinate_mixed Q 2 1
  have h12 : cubeAverage Q (fun x => diagCenteredCoordinate Q 0 x * diagCenteredCoordinate Q 1 x ^ 2) = 0 := by
    simpa only [pow_one, he, diagCenteredCoordinate_mean, zero_mul] using diagCenteredCoordinate_mixed Q 1 2
  have h22 : cubeAverage Q (fun x => diagCenteredCoordinate Q 0 x ^ 2 * diagCenteredCoordinate Q 1 x ^ 2) = 1/144 := by
    simpa only [he, show (1/12:ℝ)*(1/12)=1/144 by norm_num] using diagCenteredCoordinate_mixed Q 2 2
  fin_cases a <;> fin_cases b <;>
    norm_num [pairing, diagBilinearBasis, diagBilinearWeight, ← pow_two,
      diagCenteredCoordinate_mean, cubeAverage_const, he]
  all_goals
    solve
    | convert h11 using 1 <;> (congr 1; funext x; ring)
    | convert h21 using 1 <;> (congr 1; funext x; ring)
    | convert h12 using 1 <;> (congr 1; funext x; ring)
    | (convert h22 using 1; congr 1; funext x; ring)

/-- A bilinear polynomial in centered physical cell coordinates. -/
def diagBilinearPolynomial (Q : TriadicCube 2) (c : Fin 4 → ℝ) (x : Vec 2) : ℝ :=
  ∑ a, c a * diagBilinearBasis Q a x

/-- Exact physical-cell L² energy of a bilinear polynomial. -/
theorem diagBilinearPolynomial_energy (Q : TriadicCube 2) (c : Fin 4 → ℝ) :
    energy Q (diagBilinearPolynomial Q c) = ∑ a, c a ^ 2 * diagBilinearWeight a := by
  have hint (a b : Fin 4) : Integrable
      (fun x => c a * diagBilinearBasis Q a x * (c b * diagBilinearBasis Q b x))
      (normalizedCubeMeasure Q) :=
    (Support.ProjectedPoincare.continuous_memLp_cube Q
      ((continuous_const.mul (diagBilinearBasis_continuous Q a)).mul
        (continuous_const.mul (diagBilinearBasis_continuous Q b))) 1).integrable le_rfl
  unfold energy pairing diagBilinearPolynomial
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hint a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hint _ b)]
  have hp (a b : Fin 4) :
      (∫ x, c a * diagBilinearBasis Q a x * (c b * diagBilinearBasis Q b x)
        ∂normalizedCubeMeasure Q) = c a * c b * pairing Q (diagBilinearBasis Q a) (diagBilinearBasis Q b) := by
    simp_rw [show ∀ x, c a * diagBilinearBasis Q a x * (c b * diagBilinearBasis Q b x) =
      (c a*c b)*(diagBilinearBasis Q a x*diagBilinearBasis Q b x) from fun x => by ring]
    rw [integral_const_mul]
    rw [pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
  simp_rw [hp, diagBilinearBasis_pairing, mul_ite, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, pow_two]

end

end ASDExplicitGamma.Triadic
