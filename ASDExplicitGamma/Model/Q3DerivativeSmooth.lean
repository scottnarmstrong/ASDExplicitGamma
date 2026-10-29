module

public import ASDExplicitGamma.Model.Q3DerivativeGram
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! Global C2 regularity and polynomial jets of the literal q3 autocovariance. -/

@[expose] public section
namespace ASDExplicitGamma.Model
open MeasureTheory Set
open scoped Convolution
noncomputable section

 theorem q3Kernel_even_global (x : ℝ) : q3Kernel (-x) = q3Kernel x := by
  rw [q3Kernel, q3Kernel]
  simp only [neg_sq, abs_neg]

 theorem q3Cov_eq_realConvolution (u : ℝ) :
    q3Cov u = MeasureTheory.convolution q3Kernel q3Kernel (ContinuousLinearMap.mul ℝ ℝ) volume u := by
  rw [q3Cov, MeasureTheory.convolution_def]
  have hc := Measure.integral_comp_mul_left (fun x : ℝ => q3Kernel x*q3Kernel (u-x)) (-1)
  simpa [q3Kernel_even_global, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hc


 theorem q3Cov_contDiff_two : ContDiff ℝ 2 q3Cov := by
  have hc : ContDiff ℝ 2 (MeasureTheory.convolution q3Kernel q3Kernel (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    q3Kernel_hasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      q3Kernel_integrable.locallyIntegrable q3Kernel_contDiff_two
  rw [show q3Cov = MeasureTheory.convolution q3Kernel q3Kernel (ContinuousLinearMap.mul ℝ ℝ) volume from funext q3Cov_eq_realConvolution]
  exact hc

 def q3CovRightPolynomial : Polynomial ℝ :=
  1 - Polynomial.C (39/5)*Polynomial.X^2 + Polynomial.C (143/5)*Polynomial.X^4 -
    Polynomial.C (429/5)*Polynomial.X^6 + Polynomial.C (429/5)*Polynomial.X^7 -
    Polynomial.C (143/5)*Polynomial.X^9 + Polynomial.C (39/5)*Polynomial.X^11 - Polynomial.X^13

 theorem q3Cov_eq_rightPolynomial {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    q3Cov t = q3CovRightPolynomial.eval t := by
  rw [q3Cov_eq_polynomial_on_unit_interval t h0 h1]
  simp only [q3CovRightPolynomial, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]

 theorem polynomial_iteratedDeriv_eval (p : Polynomial ℝ) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (fun x => p.eval x) t = ((Polynomial.derivative^[n]) p).eval t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih]
    simpa only [Function.iterate_succ_apply'] using (((Polynomial.derivative^[n]) p).hasDerivAt t).deriv

 theorem q3Cov_iteratedDeriv_eq_rightPolynomial {n : ℕ} (hn : n ≤ 2) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : iteratedDeriv n q3Cov t = ((Polynomial.derivative^[n]) q3CovRightPolynomial).eval t := by
  have hs : UniqueDiffOn ℝ (Icc (0:ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have ht : t ∈ Icc (0:ℝ) 1 := ⟨h0,h1⟩
  have he : EqOn q3Cov (fun x => q3CovRightPolynomial.eval x) (Icc (0:ℝ) 1) :=
    fun x hx => q3Cov_eq_rightPolynomial hx.1 hx.2
  have hp : ContDiff ℝ n (fun x => q3CovRightPolynomial.eval x) := by
    unfold q3CovRightPolynomial
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
    fun_prop
  rw [← iteratedDerivWithin_eq_iteratedDeriv hs
    (q3Cov_contDiff_two.of_le (by exact_mod_cast hn)).contDiffAt ht,
    iteratedDerivWithin_congr he ht,
    iteratedDerivWithin_eq_iteratedDeriv hs hp.contDiffAt ht]
  exact polynomial_iteratedDeriv_eval _ _ _

end
end ASDExplicitGamma.Model
