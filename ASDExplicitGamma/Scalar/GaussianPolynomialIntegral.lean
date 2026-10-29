module

public import ASDExplicitGamma.Scalar.GaussianWick
public import Mathlib.Algebra.BigOperators.Ring.List

/-! Exact Gaussian integration of finite coordinate polynomials via Wick contractions. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian

abbrev GaussianPolynomial (n : ℕ) := List (ℝ × List (Fin n))

noncomputable def gaussianPolynomialEval {n : ℕ} (P : GaussianPolynomial n) (x : Fin n → ℝ) : ℝ :=
  (P.map (fun t => t.1*gaussianMonomial t.2 x)).sum

noncomputable def gaussianPolynomialMean {n : ℕ} (P : GaussianPolynomial n) : ℝ :=
  (P.map (fun t => t.1*gaussianWickValue t.2.length t.2)).sum

noncomputable def gaussianPolynomialMul {n : ℕ} (P Q : GaussianPolynomial n) : GaussianPolynomial n :=
  P.flatMap (fun u => Q.map (fun v => (u.1*v.1,u.2++v.2)))

noncomputable def gaussianPolynomialPow {n : ℕ} (P : GaussianPolynomial n) : ℕ → GaussianPolynomial n
  | 0 => [(1,[])]
  | k+1 => gaussianPolynomialMul (gaussianPolynomialPow P k) P

theorem integrable_gaussian_polynomial {n : ℕ} (P : GaussianPolynomial n) :
    Integrable (gaussianPolynomialEval P) (standardGaussianPi n) := by
  induction P with
  | nil =>
    change Integrable (fun _ => (0:ℝ)) _
    convert integrable_zero _ _ _ using 1
  | cons t P ih =>
    change Integrable (fun x => t.1*gaussianMonomial t.2 x+gaussianPolynomialEval P x) _
    convert ((integrable_gaussian_monomial t.2).const_mul t.1).add ih using 1

/-- Exact evaluation against the actual measure, with no integrability premise. -/
theorem integral_gaussian_polynomial_eq_mean {n : ℕ} (P : GaussianPolynomial n) :
    (∫ x, gaussianPolynomialEval P x ∂standardGaussianPi n) = gaussianPolynomialMean P := by
  induction P with
  | nil => simp only [gaussianPolynomialEval,gaussianPolynomialMean,List.map_nil,List.sum_nil,integral_zero]
  | cons t P ih =>
    change (∫ x, t.1*gaussianMonomial t.2 x+gaussianPolynomialEval P x ∂standardGaussianPi n) =
      t.1*gaussianWickValue t.2.length t.2+gaussianPolynomialMean P
    rw [integral_add ((integrable_gaussian_monomial t.2).const_mul t.1)
      (integrable_gaussian_polynomial P),integral_const_mul,ih,gaussian_integral_eq_wick_value _ _ le_rfl]

theorem gaussian_polynomial_eval_mul {n : ℕ} (P Q : GaussianPolynomial n) (x : Fin n → ℝ) :
    gaussianPolynomialEval (gaussianPolynomialMul P Q) x = gaussianPolynomialEval P x*gaussianPolynomialEval Q x := by
  induction P with
  | nil => simp only [gaussianPolynomialMul,List.flatMap_nil,gaussianPolynomialEval,List.map_nil,List.sum_nil,zero_mul]
  | cons u P ih =>
    have hEval (R S : GaussianPolynomial n) : gaussianPolynomialEval (R++S) x =
        gaussianPolynomialEval R x+gaussianPolynomialEval S x := by
      simp only [gaussianPolynomialEval,List.map_append,List.sum_append]
    rw [gaussianPolynomialMul,List.flatMap_cons,hEval]
    have he : gaussianPolynomialEval (Q.map (fun v => (u.1*v.1,u.2++v.2))) x =
        u.1*gaussianMonomial u.2 x*gaussianPolynomialEval Q x := by
      unfold gaussianPolynomialEval
      simp only [List.map_map,Function.comp_def,gaussianMonomial,List.map_append,List.prod_append]
      have ht (v : ℝ × List (Fin n)) :
          u.1*v.1*((u.2.map (fun i => x i)).prod*(v.2.map (fun i => x i)).prod) =
          (u.1*(u.2.map (fun i => x i)).prod)*(v.1*(v.2.map (fun i => x i)).prod) := by ring
      simp_rw [ht]
      exact List.sum_map_mul_left (l := Q) (r := u.1*(u.2.map (fun i => x i)).prod)
        (f := fun v : ℝ × List (Fin n) => v.1*(v.2.map (fun i => x i)).prod)
    rw [he]
    change _+gaussianPolynomialEval (gaussianPolynomialMul P Q) x =
      (u.1*gaussianMonomial u.2 x+gaussianPolynomialEval P x)*gaussianPolynomialEval Q x
    rw [ih,add_mul]

theorem gaussian_polynomial_eval_pow {n : ℕ} (P : GaussianPolynomial n) (k : ℕ) (x : Fin n → ℝ) :
    gaussianPolynomialEval (gaussianPolynomialPow P k) x = (gaussianPolynomialEval P x)^k := by
  induction k with
  | zero => simp only [gaussianPolynomialPow,gaussianPolynomialEval,gaussianMonomial,List.map_nil,List.prod_nil,
      List.map_cons,List.sum_cons,List.sum_nil,mul_one,add_zero,pow_zero]
  | succ k ih => rw [gaussianPolynomialPow,gaussian_polynomial_eval_mul,ih,pow_succ]

theorem gaussian_polynomial_eval_append {n : ℕ} (P Q : GaussianPolynomial n) (x : Fin n → ℝ) :
    gaussianPolynomialEval (P++Q) x = gaussianPolynomialEval P x+gaussianPolynomialEval Q x := by
  simp only [gaussianPolynomialEval,List.map_append,List.sum_append]

theorem gaussian_polynomial_eval_flatten {n : ℕ} (Ps : List (GaussianPolynomial n)) (x : Fin n → ℝ) :
    gaussianPolynomialEval Ps.flatten x = (Ps.map (fun P => gaussianPolynomialEval P x)).sum := by
  induction Ps with
  | nil => simp only [List.flatten_nil,gaussianPolynomialEval,List.map_nil,List.sum_nil]
  | cons P Ps ih => simp only [List.flatten_cons,gaussian_polynomial_eval_append,ih,List.map_cons,List.sum_cons]

end ASDExplicitGamma.Scalar
