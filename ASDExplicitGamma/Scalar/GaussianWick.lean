module

public import ASDExplicitGamma.Scalar.GaussianPolynomialBounds

/-! Wick recursion from genuine product Gaussian integration by parts.
Deletion lists keep the Kronecker factors literal, including repeated coordinates. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian

/-- All contractions of one coordinate against a coordinate monomial. -/
def gaussianContractions {n : ℕ} (i : Fin n) : List (Fin n) → List (List (Fin n))
  | [] => []
  | j::a => (if i=j then [a] else []) ++ (gaussianContractions i a).map (j::·)

/-- A contracted monomial has strictly smaller degree than its input. -/
theorem gaussian_contraction_length {n : ℕ} (i : Fin n) (a b : List (Fin n))
    (hb : b ∈ gaussianContractions i a) : b.length+1 = a.length := by
  induction a generalizing b with
  | nil => simp only [gaussianContractions,List.not_mem_nil] at hb
  | cons j a ih =>
    simp only [gaussianContractions,List.mem_append,List.mem_map] at hb
    rcases hb with hb | ⟨c,hc,rfl⟩
    · split_ifs at hb
      · simp only [List.mem_singleton] at hb
        subst b
        rfl
      · exact False.elim (List.not_mem_nil hb)
    · have hh := ih c hc
      simp only [List.length_cons]
      omega

/-- Coordinate derivatives of a monomial are exactly its contraction list. -/
theorem gaussian_monomial_derivative {n : ℕ} (a : List (Fin n)) (i : Fin n)
    (x : Fin n → ℝ) :
    coordinateDerivative (gaussianMonomial a) i x =
      ((gaussianContractions i a).map (fun b => gaussianMonomial b x)).sum := by
  induction a with
  | nil =>
    have he : gaussianMonomial ([] : List (Fin n)) = fun _ => (1:ℝ) := by funext y; rfl
    rw [he]
    simp [coordinateDerivative,gaussianContractions]
  | cons j a ih =>
    have he : gaussianMonomial (j::a) = fun y => y j*gaussianMonomial a y := by funext y; rfl
    rw [he,gaussian_coordinate_derivative_mul (by fun_prop)
      ((gaussian_monomial_coordinate_bound a).1.differentiable (by norm_num))]
    have hd : coordinateDerivative (fun y : Fin n → ℝ => y j) i x = if i=j then 1 else 0 := by
      unfold coordinateDerivative
      rw [(hasFDerivAt_apply j x).fderiv]
      simp only [ContinuousLinearMap.proj_apply,Pi.single_apply,eq_comm]
    rw [hd,ih]
    simp only [gaussianContractions,List.map_append,List.sum_append,List.map_map,Function.comp_def]
    have hmul : ((gaussianContractions i a).map (fun b => gaussianMonomial (j::b) x)).sum =
        x j*((gaussianContractions i a).map (fun b => gaussianMonomial b x)).sum := by
      induction gaussianContractions i a with
      | nil => simp only [List.map_nil,List.sum_nil,mul_zero]
      | cons b bs ihbs =>
        simp only [List.map_cons,List.sum_cons,gaussianMonomial,List.prod_cons] at ihbs ⊢
        rw [ihbs,mul_add]
    rw [hmul]
    split_ifs <;> simp only [List.map_nil,List.sum_nil,List.map_cons,List.sum_cons,
      zero_add,one_mul,zero_mul,add_zero]

/-- Finite integration commutes with the actual list of Gaussian monomials. -/
theorem integral_gaussian_monomial_sum {n : ℕ} (bs : List (List (Fin n))) :
    (∫ x, (bs.map (fun b => gaussianMonomial b x)).sum ∂standardGaussianPi n) =
      (bs.map (fun b => ∫ x, gaussianMonomial b x ∂standardGaussianPi n)).sum := by
  have hInt (cs : List (List (Fin n))) :
      Integrable (fun x => (cs.map (fun b => gaussianMonomial b x)).sum) (standardGaussianPi n) := by
    induction cs with
    | nil => exact integrable_zero _ _ _
    | cons c cs ihcs =>
      simp only [List.map_cons,List.sum_cons]
      convert (integrable_gaussian_monomial c).add ihcs using 1
  induction bs with
  | nil => simp only [List.map_nil,List.sum_nil,integral_zero]
  | cons b bs ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (integrable_gaussian_monomial b) (hInt bs),ih]

/-- The Wick recursion is an identity for genuine Gaussian integrals, not an assumed functional. -/
theorem gaussian_monomial_wick_recursion {n : ℕ} (i : Fin n) (a : List (Fin n)) :
    (∫ x, gaussianMonomial (i::a) x ∂standardGaussianPi n) =
      ((gaussianContractions i a).map (fun b => ∫ x, gaussianMonomial b x ∂standardGaussianPi n)).sum := by
  have h := integral_eval_mul_eq_integral_coordinateDerivative (gaussian_monomial_coordinate_bound a) i
  have hleft : (fun x : Fin n → ℝ => x i*gaussianMonomial a x) = gaussianMonomial (i::a) := by
    funext x
    rfl
  rw [hleft] at h
  rw [h]
  simp_rw [gaussian_monomial_derivative]
  exact integral_gaussian_monomial_sum _

/-- A finite evaluator for the Wick contractions; the fuel is at least the degree. -/
noncomputable def gaussianWickValue {n : ℕ} : ℕ → List (Fin n) → ℝ
  | _, [] => 1
  | 0, _::_ => 0
  | fuel+1, i::a => ((gaussianContractions i a).map (gaussianWickValue fuel)).sum

/-- The finite Wick evaluator computes actual Gaussian integrals exactly. -/
theorem gaussian_integral_eq_wick_value {n : ℕ} (fuel : ℕ) (a : List (Fin n))
    (hlen : a.length ≤ fuel) :
    (∫ x, gaussianMonomial a x ∂standardGaussianPi n) = gaussianWickValue fuel a := by
  have instStandardGaussianProbability : IsProbabilityMeasure (standardGaussianPi n) := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
    infer_instance
  induction fuel generalizing a with
  | zero =>
    have ha : a = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst a
    simp [gaussianMonomial,gaussianWickValue]
  | succ fuel ih =>
    cases a with
    | nil => simp [gaussianMonomial,gaussianWickValue]
    | cons i a =>
      rw [gaussian_monomial_wick_recursion]
      change ((gaussianContractions i a).map (fun b => ∫ x, gaussianMonomial b x ∂standardGaussianPi n)).sum =
        ((gaussianContractions i a).map (gaussianWickValue fuel)).sum
      congr 1
      apply List.map_congr_left
      intro b hb
      apply ih
      have hh := gaussian_contraction_length i a b hb
      simp only [List.length_cons] at hlen
      omega

end ASDExplicitGamma.Scalar
