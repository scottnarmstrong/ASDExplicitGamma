/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.ConcentrationGeneral
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Gaussian concentration for finite maxima

The log-sum-exp approximation used to pass from smooth functions to finite maxima.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open Filter
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- Log-sum-exp smoothing of a finite family of linear forms on a product space. -/
noncomputable def gaussianFiniteLogSumExp {m n : ℕ} (β : ℝ)
    (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.log (∑ i : Fin m, Real.exp (β * ∑ j : Fin n, a i j * x j)) / β

/-- The linear form associated with a coefficient vector. -/
def gaussianFiniteLinearForm {n : ℕ} (a : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, a j * x j

/-- A linear form under the product standard Gaussian is centered and has variance equal to the
square of its Euclidean coefficient norm. -/
theorem integral_variance_gaussianFiniteLinearForm {n : ℕ} (a : Fin n → ℝ) :
    (∫ x, gaussianFiniteLinearForm a x ∂(standardGaussianPi n)) = 0 ∧
      Var[gaussianFiniteLinearForm a; standardGaussianPi n] =
        ‖WithLp.toLp 2 a‖ ^ 2 := by
  let E := EuclideanSpace ℝ (Fin n)
  let v : E := WithLp.toLp 2 a
  let L : StrongDual ℝ E := innerSL ℝ v
  have hmap : (standardGaussianPi n).map (WithLp.toLp 2) = stdGaussian E := by
    simpa [standardGaussianPi, E] using
      (ProbabilityTheory.map_pi_eq_stdGaussian (ι := Fin n))
  have hfun (x : Fin n → ℝ) : gaussianFiniteLinearForm a x = L (WithLp.toLp 2 x) := by
    change (∑ j : Fin n, a j * x j) = ⟪v, WithLp.toLp 2 x⟫
    rw [EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, mul_comm]
  have hmean : (∫ x, gaussianFiniteLinearForm a x ∂(standardGaussianPi n)) = 0 := by
    calc
      _ = ∫ x, L (WithLp.toLp 2 x) ∂(standardGaussianPi n) := by
        apply integral_congr_ae
        exact ae_of_all _ hfun
      _ = ∫ y, L y ∂(standardGaussianPi n).map (WithLp.toLp 2) :=
        (integral_map (by fun_prop) (by fun_prop)).symm
      _ = 0 := by rw [hmap]; exact ProbabilityTheory.integral_strongDual_stdGaussian L
  have hvariance : Var[gaussianFiniteLinearForm a; standardGaussianPi n] = ‖v‖ ^ 2 := by
    calc
      _ = Var[L ∘ WithLp.toLp 2; standardGaussianPi n] := by
        congr 1
        funext x
        exact hfun x
      _ = Var[L; (standardGaussianPi n).map (WithLp.toLp 2)] :=
        (variance_map (L.continuous.aemeasurable) (by fun_prop)).symm
      _ = ‖v‖ ^ 2 := by
        rw [hmap, ProbabilityTheory.variance_dual_stdGaussian]
        simp [L, innerSL_apply_norm]
  exact ⟨hmean, by simpa [v] using hvariance⟩

/-- The maximum of a nonempty finite family of Gaussian linear forms. -/
noncomputable def gaussianFiniteMaximum {m n : ℕ} (hm : 0 < m)
    (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin m)).sup'
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩ fun i => gaussianFiniteLinearForm (a i) x

private noncomputable def gaussianFiniteLinearFormFDeriv {n : ℕ} (a : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ j : Fin n, a j •
    (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)

private theorem hasFDerivAt_gaussianFiniteLinearForm {n : ℕ}
    (a : Fin n → ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (gaussianFiniteLinearForm a) (gaussianFiniteLinearFormFDeriv a) x := by
  classical
  have hterm (j : Fin n) : HasFDerivAt (fun y : Fin n → ℝ => a j * y j)
      (a j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    simpa using ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt).const_mul (a j)
  convert HasFDerivAt.sum (u := Finset.univ) (fun j hj => hterm j) using 1
  · ext y
    simp [gaussianFiniteLinearForm]
  · simp [gaussianFiniteLinearFormFDeriv]

private theorem coordinateDerivative_gaussianFiniteLinearForm {n : ℕ}
    (a : Fin n → ℝ) (j : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (gaussianFiniteLinearForm a) j x = a j := by
  rw [coordinateDerivative, (hasFDerivAt_gaussianFiniteLinearForm a x).fderiv]
  simp only [gaussianFiniteLinearFormFDeriv, sum_apply, smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [hkj]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

private theorem deriv_update_comp_eq_coordinateDerivative {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 1 F) (x : Fin n → ℝ)
    (i : Fin n) (t : ℝ) :
    deriv (fun s => F (Function.update x i s)) t =
      coordinateDerivative F i (Function.update x i t) := by
  have hcomp := (hF.differentiable_one (Function.update x i t)).hasFDerivAt.comp t
    (hasDerivAt_update x i t).hasFDerivAt
  have hderiv := hcomp.hasDerivAt.deriv
  simpa [Function.comp_def, coordinateDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply] using hderiv

private theorem hasDerivAt_gaussianFiniteLinearForm_update {n : ℕ}
    (a : Fin n → ℝ) (x : Fin n → ℝ) (k : Fin n) :
    HasDerivAt (fun t => gaussianFiniteLinearForm a (Function.update x k t))
      (a k) (x k) := by
  have hcomp := (hasFDerivAt_gaussianFiniteLinearForm a
    (Function.update x k (x k))).comp_hasDerivAt (x k)
      (hasDerivAt_update x k (x k))
  have hcoord := coordinateDerivative_gaussianFiniteLinearForm a k
    (Function.update x k (x k))
  have hderiv :
      gaussianFiniteLinearFormFDeriv a (Pi.single k (1 : ℝ)) = a k := by
    change fderiv ℝ (gaussianFiniteLinearForm a) (Function.update x k (x k))
      (Pi.single k (1 : ℝ)) = a k at hcoord
    rw [(hasFDerivAt_gaussianFiniteLinearForm a
      (Function.update x k (x k))).fderiv] at hcoord
    exact hcoord
  convert hcomp using 1
  · ext t
    rfl
  · exact hderiv.symm

private theorem hasDerivAt_gaussianFiniteExpTerm_update {m n : ℕ}
    (β : ℝ) (a : Fin m → Fin n → ℝ) (i : Fin m) (x : Fin n → ℝ)
    (k : Fin n) :
    HasDerivAt (fun t => Real.exp (β * gaussianFiniteLinearForm (a i)
        (Function.update x k t)))
      (Real.exp (β * gaussianFiniteLinearForm (a i)
        (Function.update x k (x k))) * (β * a i k)) (x k) := by
  exact (hasDerivAt_gaussianFiniteLinearForm_update (a i) x k).const_mul β |>.exp

private theorem gaussianFiniteLogSumExp_denominator_pos {m n : ℕ} (hm : 0 < m)
    (β : ℝ) (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    0 < ∑ i : Fin m, Real.exp (β * ∑ j : Fin n, a i j * x j) := by
  classical
  apply Finset.sum_pos'
  · intro i hi
    exact (Real.exp_pos _).le
  · refine ⟨⟨0, hm⟩, Finset.mem_univ _, Real.exp_pos _⟩

private noncomputable def gaussianFiniteLogSumExpDenom {m n : ℕ} (β : ℝ)
    (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, Real.exp (β * gaussianFiniteLinearForm (a i) x)

private noncomputable def gaussianFiniteSoftmaxWeight {m n : ℕ} (β : ℝ)
    (a : Fin m → Fin n → ℝ) (i : Fin m) (x : Fin n → ℝ) : ℝ :=
  Real.exp (β * gaussianFiniteLinearForm (a i) x) / gaussianFiniteLogSumExpDenom β a x

private theorem contDiff_gaussianFiniteSoftmaxWeight {m n : ℕ} (hm : 0 < m)
    (β : ℝ) (a : Fin m → Fin n → ℝ) (i : Fin m) :
    ContDiff ℝ 3 (gaussianFiniteSoftmaxWeight β a i) := by
  change ContDiff ℝ 3 (fun x : Fin n → ℝ =>
    Real.exp (β * ∑ j : Fin n, a i j * x j) /
      ∑ i : Fin m, Real.exp (β * ∑ j : Fin n, a i j * x j))
  have hnum : ContDiff ℝ 3 (fun x : Fin n → ℝ =>
      Real.exp (β * ∑ j : Fin n, a i j * x j)) := by fun_prop
  have hden : ContDiff ℝ 3 (fun x : Fin n → ℝ =>
      ∑ i : Fin m, Real.exp (β * ∑ j : Fin n, a i j * x j)) := by fun_prop
  exact hnum.div hden fun x =>
    (gaussianFiniteLogSumExp_denominator_pos hm β a x).ne'

/-- Log-sum-exp is smooth of every finite order, since its exponential sum is strictly positive. -/
theorem contDiff_gaussianFiniteLogSumExp {m n : ℕ} (hm : 0 < m) (β : ℝ)
    (a : Fin m → Fin n → ℝ) :
    ContDiff ℝ 3 (gaussianFiniteLogSumExp β a) := by
  have hsum : ContDiff ℝ 3
      (fun x : Fin n → ℝ =>
        ∑ i : Fin m, Real.exp (β * ∑ j : Fin n, a i j * x j)) := by
    fun_prop
  have hlog : ContDiff ℝ 3
      (fun x : Fin n → ℝ =>
        Real.log (∑ i : Fin m, Real.exp (β * ∑ j : Fin n, a i j * x j))) :=
    hsum.log fun x => (gaussianFiniteLogSumExp_denominator_pos hm β a x).ne'
  change ContDiff ℝ 3
    (fun x : Fin n → ℝ =>
      Real.log (∑ i : Fin m, Real.exp (β * ∑ j : Fin n, a i j * x j)) / β)
  exact hlog.div_const β

private theorem coordinateDerivative_gaussianFiniteSoftmaxWeight {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (a : Fin m → Fin n → ℝ) (i : Fin m)
    (k : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k x =
      β * gaussianFiniteSoftmaxWeight β a i x *
        (a i k - ∑ j : Fin m, gaussianFiniteSoftmaxWeight β a j x * a j k) := by
  have hweightSlice := deriv_update_comp_eq_coordinateDerivative
    ((contDiff_gaussianFiniteSoftmaxWeight hm β a i).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) x k (x k)
  have hcoord : coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k x =
      deriv (fun t => gaussianFiniteSoftmaxWeight β a i (Function.update x k t)) (x k) := by
    simpa using hweightSlice.symm
  rw [hcoord]
  have hnum := hasDerivAt_gaussianFiniteExpTerm_update β a i x k
  have hDpos := gaussianFiniteLogSumExp_denominator_pos hm β a x
  have hDne : gaussianFiniteLogSumExpDenom β a x ≠ 0 := hDpos.ne'
  have hdenomHas : HasDerivAt
      (fun t => gaussianFiniteLogSumExpDenom β a (Function.update x k t))
      (∑ j : Fin m,
        Real.exp (β * gaussianFiniteLinearForm (a j)
          (Function.update x k (x k))) * (β * a j k)) (x k) := by
    change HasDerivAt (fun t : ℝ =>
      ∑ j : Fin m, Real.exp (β * gaussianFiniteLinearForm (a j)
        (Function.update x k t))) _ _
    exact HasDerivAt.fun_sum (u := Finset.univ)
      (fun j hj => hasDerivAt_gaussianFiniteExpTerm_update β a j x k)
  change deriv (fun t : ℝ =>
      Real.exp (β * gaussianFiniteLinearForm (a i) (Function.update x k t)) /
        gaussianFiniteLogSumExpDenom β a (Function.update x k t)) (x k) = _
  change deriv
      ((fun t : ℝ => Real.exp (β * gaussianFiniteLinearForm (a i)
        (Function.update x k t))) /
       (fun t : ℝ => gaussianFiniteLogSumExpDenom β a (Function.update x k t))) (x k) = _
  rw [deriv_div hnum.differentiableAt hdenomHas.differentiableAt
    (by simpa [Function.update_self] using hDne), hnum.deriv, hdenomHas.deriv]
  simp only [Function.update_eq_self]
  unfold gaussianFiniteSoftmaxWeight gaussianFiniteLogSumExpDenom
  have hsumβ :
      (∑ j : Fin m,
        Real.exp (β * gaussianFiniteLinearForm (a j) x) * (β * a j k)) =
      β * ∑ j : Fin m, Real.exp (β * gaussianFiniteLinearForm (a j) x) * a j k := by
    calc
      _ = ∑ j : Fin m,
          β * (Real.exp (β * gaussianFiniteLinearForm (a j) x) * a j k) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hsumfrac :
      (∑ j : Fin m,
        (Real.exp (β * gaussianFiniteLinearForm (a j) x) /
          ∑ l : Fin m, Real.exp (β * gaussianFiniteLinearForm (a l) x)) * a j k) =
      (∑ j : Fin m,
        Real.exp (β * gaussianFiniteLinearForm (a j) x) * a j k) /
        ∑ l : Fin m, Real.exp (β * gaussianFiniteLinearForm (a l) x) := by
    calc
      _ = ∑ j : Fin m,
          (Real.exp (β * gaussianFiniteLinearForm (a j) x) * a j k) /
            ∑ l : Fin m, Real.exp (β * gaussianFiniteLinearForm (a l) x) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.sum_div]
  have hnum :
      Real.exp (β * gaussianFiniteLinearForm (a i) x) * (β * a i k) *
          (∑ j : Fin m, Real.exp (β * gaussianFiniteLinearForm (a j) x)) =
        β * Real.exp (β * gaussianFiniteLinearForm (a i) x) * a i k *
          (∑ j : Fin m, Real.exp (β * gaussianFiniteLinearForm (a j) x)) := by
    ring
  rw [hnum, hsumβ, hsumfrac]
  have hS : (∑ j : Fin m,
      Real.exp (β * gaussianFiniteLinearForm (a j) x)) ≠ 0 := by
    simpa [gaussianFiniteLogSumExpDenom] using hDne
  field_simp [hS]

private theorem contDiff_coordinateDerivative_gaussianFiniteSoftmaxWeight {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (a : Fin m → Fin n → ℝ) (i : Fin m) (k : Fin n) :
    ContDiff ℝ 2 (coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k) := by
  have h := (contDiff_gaussianFiniteSoftmaxWeight hm β a i).contDiff_fderiv_apply
    (m := 2) (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hp : ContDiff ℝ 2
      (fun x : Fin n → ℝ => (x, (Pi.single k (1 : ℝ) : Fin n → ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hc := h.comp hp
  convert hc using 1
  · ext x
    rfl

private theorem coordinateDerivative_finset_sum_mul_const {m n : ℕ}
    (p : Fin m → (Fin n → ℝ) → ℝ) (c : Fin m → ℝ)
    (hp : ∀ i, ContDiff ℝ 1 (p i)) (k : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (fun y => ∑ i : Fin m, p i y * c i) k x =
      ∑ i : Fin m, coordinateDerivative (p i) k x * c i := by
  rw [coordinateDerivative, fderiv_fun_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    have hdi : DifferentiableAt ℝ (p i) x := (hp i).differentiable_one x
    have h := congrArg
      (fun T : (Fin n → ℝ) →L[ℝ] ℝ => T (Pi.single k (1 : ℝ)))
      (fderiv_mul_const hdi (c i))
    simpa [coordinateDerivative, smul_eq_mul, mul_comm] using h
  · intro i hi
    exact ((hp i).differentiable_one x).mul_const (c i)

private theorem coordinateDerivative_const_mul_maxima {n : ℕ}
    (c : ℝ) (f : (Fin n → ℝ) → ℝ) (k : Fin n) (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ f x) :
    coordinateDerivative (fun y => c * f y) k x = c * coordinateDerivative f k x := by
  rw [coordinateDerivative, fderiv_const_mul hf c]
  simp [coordinateDerivative, smul_eq_mul]

private theorem coordinateDerivative_mul_maxima {n : ℕ}
    (f g : (Fin n → ℝ) → ℝ) (k : Fin n) (x : Fin n → ℝ)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    coordinateDerivative (fun y => f y * g y) k x =
      f x * coordinateDerivative g k x + g x * coordinateDerivative f k x := by
  rw [coordinateDerivative, fderiv_fun_mul hf hg]
  simp [coordinateDerivative, smul_eq_mul]

private theorem coordinateDerivative_const_sub_maxima {n : ℕ}
    (c : ℝ) (f : (Fin n → ℝ) → ℝ) (k : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (fun y => c - f y) k x =
      -coordinateDerivative f k x := by
  rw [coordinateDerivative, fderiv_const_sub c]
  simp [coordinateDerivative]

private theorem contDiff_coordinateDerivative_of_three_maxima {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 3 F) (i : Fin n) :
    ContDiff ℝ 2 (coordinateDerivative F i) := by
  have h := hF.contDiff_fderiv_apply (m := 2)
    (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hp : ContDiff ℝ 2
      (fun x : Fin n → ℝ => (x, (Pi.single i (1 : ℝ) : Fin n → ℝ))) :=
    contDiff_id.prodMk contDiff_const
  convert h.comp hp using 1
  · ext x
    rfl

private theorem fderiv_gaussianFiniteLogSumExpDenom {m n : ℕ}
    (β : ℝ) (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    fderiv ℝ (gaussianFiniteLogSumExpDenom β a) x =
      ∑ i : Fin m,
        (β * Real.exp (β * gaussianFiniteLinearForm (a i) x)) •
          gaussianFiniteLinearFormFDeriv (a i) := by
  classical
  have hline (i : Fin m) : DifferentiableAt ℝ (gaussianFiniteLinearForm (a i)) x :=
    (hasFDerivAt_gaussianFiniteLinearForm (a i) x).differentiableAt
  have hterm (i : Fin m) : DifferentiableAt ℝ
      (fun y : Fin n → ℝ => Real.exp (β * gaussianFiniteLinearForm (a i) y)) x :=
    (hline i).const_mul β |>.exp
  change fderiv ℝ
    (fun y : Fin n → ℝ =>
      ∑ i : Fin m, Real.exp (β * gaussianFiniteLinearForm (a i) y)) x = _
  rw [fderiv_fun_sum (u := Finset.univ) (fun i hi => hterm i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fderiv_exp ((hline i).const_mul β), fderiv_const_mul (hline i) β,
    (hasFDerivAt_gaussianFiniteLinearForm (a i) x).fderiv]
  rw [smul_smul]
  congr 1
  ring

private theorem fderiv_gaussianFiniteLogSumExp {m n : ℕ} (hm : 0 < m)
    (β : ℝ) (hβ : β ≠ 0) (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    fderiv ℝ (gaussianFiniteLogSumExp β a) x =
      ∑ i : Fin m,
        gaussianFiniteSoftmaxWeight β a i x • gaussianFiniteLinearFormFDeriv (a i) := by
  classical
  have hdenom : 0 < gaussianFiniteLogSumExpDenom β a x := by
    simpa [gaussianFiniteLogSumExpDenom, gaussianFiniteLinearForm] using
      gaussianFiniteLogSumExp_denominator_pos hm β a x
  have hdenom_ne : gaussianFiniteLogSumExpDenom β a x ≠ 0 := hdenom.ne'
  have hdenom_diff : DifferentiableAt ℝ (gaussianFiniteLogSumExpDenom β a) x := by
    change DifferentiableAt ℝ (fun y : Fin n → ℝ =>
      ∑ i : Fin m, Real.exp (β * gaussianFiniteLinearForm (a i) y)) x
    apply DifferentiableAt.fun_sum
    intro i hi
    have hline : DifferentiableAt ℝ (gaussianFiniteLinearForm (a i)) x :=
      (hasFDerivAt_gaussianFiniteLinearForm (a i) x).differentiableAt
    exact (hline.const_mul β).exp
  have hlog_diff : DifferentiableAt ℝ
      (fun y : Fin n → ℝ => Real.log (gaussianFiniteLogSumExpDenom β a y)) x :=
    hdenom_diff.log (by simpa using hdenom_ne)
  have hdef : gaussianFiniteLogSumExp β a = fun y =>
      Real.log (gaussianFiniteLogSumExpDenom β a y) / β := by
    funext y
    simp [gaussianFiniteLogSumExp, gaussianFiniteLogSumExpDenom,
      gaussianFiniteLinearForm]
  rw [hdef]
  change fderiv ℝ
    (fun y : Fin n → ℝ => Real.log (gaussianFiniteLogSumExpDenom β a y) * β⁻¹) x = _
  rw [fderiv_mul_const hlog_diff β⁻¹, fderiv.log hdenom_diff
    (by simpa using hdenom_ne), fderiv_gaussianFiniteLogSumExpDenom]
  ext v
  simp only [sum_apply, smul_apply, smul_eq_mul,
    gaussianFiniteSoftmaxWeight, gaussianFiniteLogSumExpDenom]
  have hsum : (∑ i : Fin m,
      β * Real.exp (β * gaussianFiniteLinearForm (a i) x) *
        gaussianFiniteLinearFormFDeriv (a i) v) =
      β * ∑ i : Fin m,
        Real.exp (β * gaussianFiniteLinearForm (a i) x) *
          gaussianFiniteLinearFormFDeriv (a i) v := by
    calc
      _ = ∑ i : Fin m,
          β * (Real.exp (β * gaussianFiniteLinearForm (a i) x) *
            gaussianFiniteLinearFormFDeriv (a i) v) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [Finset.mul_sum]
  calc
    β⁻¹ * ((∑ i : Fin m, Real.exp (β * gaussianFiniteLinearForm (a i) x))⁻¹ *
        ∑ i : Fin m,
          (β * Real.exp (β * gaussianFiniteLinearForm (a i) x)) *
            gaussianFiniteLinearFormFDeriv (a i) v) =
      (∑ i : Fin m, Real.exp (β * gaussianFiniteLinearForm (a i) x) *
        gaussianFiniteLinearFormFDeriv (a i) v) /
        (∑ i : Fin m, Real.exp (β * gaussianFiniteLinearForm (a i) x)) := by
      rw [hsum]
      field_simp [hβ, ne_of_gt (gaussianFiniteLogSumExp_denominator_pos hm β a x)]
    _ = ∑ i : Fin m,
        (Real.exp (β * gaussianFiniteLinearForm (a i) x) /
          ∑ i : Fin m, Real.exp (β * gaussianFiniteLinearForm (a i) x)) *
          gaussianFiniteLinearFormFDeriv (a i) v := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring

private theorem coordinateDerivative_gaussianFiniteLogSumExp {m n : ℕ} (hm : 0 < m)
    (β : ℝ) (hβ : β ≠ 0) (a : Fin m → Fin n → ℝ) (j : Fin n)
    (x : Fin n → ℝ) :
    coordinateDerivative (gaussianFiniteLogSumExp β a) j x =
      ∑ i : Fin m, gaussianFiniteSoftmaxWeight β a i x * a i j := by
  rw [coordinateDerivative, fderiv_gaussianFiniteLogSumExp hm β hβ a x]
  simp only [gaussianFiniteLinearFormFDeriv, sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    simp [hkj]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

private theorem coordinateDerivative_gaussianFiniteLogSumExp_second {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : β ≠ 0) (a : Fin m → Fin n → ℝ)
    (j k : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) j) k x =
      ∑ i : Fin m, coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k x * a i j := by
  have hrepr : coordinateDerivative (gaussianFiniteLogSumExp β a) j =
      fun y => ∑ i : Fin m, gaussianFiniteSoftmaxWeight β a i y * a i j := by
    funext y
    exact coordinateDerivative_gaussianFiniteLogSumExp hm β hβ a j y
  rw [hrepr]
  exact coordinateDerivative_finset_sum_mul_const
    (p := fun i => gaussianFiniteSoftmaxWeight β a i)
    (c := fun i => a i j)
    (hp := fun i => (contDiff_gaussianFiniteSoftmaxWeight hm β a i).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 3)) k x

private theorem coordinateDerivative_gaussianFiniteLogSumExp_third {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : β ≠ 0) (a : Fin m → Fin n → ℝ)
    (j k l : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative
      (coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) j) k) l x =
      ∑ i : Fin m,
        coordinateDerivative (coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k) l x *
          a i j := by
  have hrepr :
      coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) j) k =
        fun y => ∑ i : Fin m,
          coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k y * a i j := by
    funext y
    exact coordinateDerivative_gaussianFiniteLogSumExp_second hm β hβ a j k y
  rw [hrepr]
  exact coordinateDerivative_finset_sum_mul_const
    (p := fun i => coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k)
    (c := fun i => a i j)
    (hp := fun i => (contDiff_coordinateDerivative_gaussianFiniteSoftmaxWeight hm β a i k).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) l x

private theorem coordinateDerivative_gaussianFiniteSoftmaxWeight_second {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : β ≠ 0) (a : Fin m → Fin n → ℝ)
    (i : Fin m) (k l : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k) l x =
      β * (coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) l x *
        (a i k - coordinateDerivative (gaussianFiniteLogSumExp β a) k x) -
        gaussianFiniteSoftmaxWeight β a i x *
          coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) k) l x) := by
  have hrepr : coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k =
      fun y => β * gaussianFiniteSoftmaxWeight β a i y *
        (a i k - coordinateDerivative (gaussianFiniteLogSumExp β a) k y) := by
    funext y
    rw [coordinateDerivative_gaussianFiniteSoftmaxWeight hm β a i k y,
      coordinateDerivative_gaussianFiniteLogSumExp hm β hβ a k y]
  rw [hrepr]
  have hp : DifferentiableAt ℝ (gaussianFiniteSoftmaxWeight β a i) x :=
    ((contDiff_gaussianFiniteSoftmaxWeight hm β a i).of_le
      (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).differentiable_one x
  have hqcont : ContDiff ℝ 2
      (coordinateDerivative (gaussianFiniteLogSumExp β a) k) :=
    contDiff_coordinateDerivative_of_three_maxima
      (contDiff_gaussianFiniteLogSumExp hm β a) k
  have hq : DifferentiableAt ℝ
      (coordinateDerivative (gaussianFiniteLogSumExp β a) k) x :=
    (hqcont.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiable_one x
  have hf : DifferentiableAt ℝ
      (fun y => β * gaussianFiniteSoftmaxWeight β a i y) x := hp.const_mul β
  have hg : DifferentiableAt ℝ
      (fun y => a i k - coordinateDerivative (gaussianFiniteLogSumExp β a) k y) x :=
    hq.const_sub (a i k)
  rw [coordinateDerivative_mul_maxima _ _ l x hf hg,
    coordinateDerivative_const_mul_maxima β _ l x hp,
    coordinateDerivative_const_sub_maxima (a i k) _ l x]
  ring

private theorem gaussianFiniteSoftmaxWeight_nonneg {m n : ℕ} (hm : 0 < m)
    (β : ℝ) (a : Fin m → Fin n → ℝ) (i : Fin m) (x : Fin n → ℝ) :
    0 ≤ gaussianFiniteSoftmaxWeight β a i x := by
  unfold gaussianFiniteSoftmaxWeight
  exact div_nonneg (Real.exp_nonneg _) (le_of_lt <| by
    simpa [gaussianFiniteLogSumExpDenom, gaussianFiniteLinearForm] using
      gaussianFiniteLogSumExp_denominator_pos hm β a x)

private theorem gaussianFiniteSoftmaxWeight_sum_eq_one {m n : ℕ} (hm : 0 < m)
    (β : ℝ) (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin m, gaussianFiniteSoftmaxWeight β a i x) = 1 := by
  have hD : 0 < gaussianFiniteLogSumExpDenom β a x := by
    simpa [gaussianFiniteLogSumExpDenom, gaussianFiniteLinearForm] using
      gaussianFiniteLogSumExp_denominator_pos hm β a x
  simp_rw [gaussianFiniteSoftmaxWeight]
  rw [← Finset.sum_div]
  unfold gaussianFiniteLogSumExpDenom
  exact div_self hD.ne'

private theorem abs_coordinate_le_euclidean_norm_local {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) : |v i| ≤ ‖v‖ := by
  have hsum : (‖v i‖ : ℝ) ^ 2 ≤ ∑ j : Fin n, (‖v j‖ : ℝ) ^ 2 :=
    Finset.single_le_sum (fun j hj => sq_nonneg (‖v j‖)) (Finset.mem_univ i)
  rw [EuclideanSpace.norm_eq]
  rw [← Real.norm_eq_abs]
  exact (Real.le_sqrt (norm_nonneg (v i)) (by positivity)).2 hsum

private theorem gaussianFiniteLinearForm_coordinate_abs_le {m n : ℕ}
    (a : Fin m → Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) (i : Fin m) (j : Fin n) :
    |a i j| ≤ L := by
  have h := abs_coordinate_le_euclidean_norm_local (WithLp.toLp 2 (a i)) j
  have h' : |(WithLp.toLp 2 (a i) : EuclideanSpace ℝ (Fin n)) j| ≤ L := h.trans (hcoeff i)
  simpa using h'

/-- A finite Gaussian linear form is bounded by its Euclidean coefficient norm times the
Euclidean input norm, with a coarse coordinate estimate for the product-space presentation. -/
theorem gaussianFiniteLinearForm_abs_le {m n : ℕ}
    (a : Fin m → Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) (i : Fin m) (x : Fin n → ℝ) :
    |gaussianFiniteLinearForm (a i) x| ≤ (n : ℝ) * L * ‖x‖ := by
  have hL : 0 ≤ L := by
    exact (norm_nonneg (WithLp.toLp 2 (a i))).trans (hcoeff i)
  calc
    |gaussianFiniteLinearForm (a i) x| ≤
        ∑ j : Fin n, |a i j * x j| := by
      simp only [gaussianFiniteLinearForm]
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, L * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j hj
      have ha : |a i j| ≤ L := gaussianFiniteLinearForm_coordinate_abs_le a hcoeff i j
      have hx : |x j| ≤ ‖x‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
      calc
        |a i j * x j| = |a i j| * |x j| := abs_mul _ _
        _ ≤ L * ‖x‖ := mul_le_mul ha hx (abs_nonneg _) hL
    _ = (n : ℝ) * L * ‖x‖ := by
      simp [Finset.sum_const, mul_assoc]

private theorem abs_gaussianFiniteLogSumExp_le_linear {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : 0 < β) (a : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) :
    |gaussianFiniteLogSumExp β a x| ≤
      Real.log (m : ℝ) / β + (n : ℝ) * L * ‖x‖ := by
  let R : ℝ := (n : ℝ) * L * ‖x‖
  have hL : 0 ≤ L := (norm_nonneg (WithLp.toLp 2 (a ⟨0, hm⟩))).trans (hcoeff ⟨0, hm⟩)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hlin (i : Fin m) : |gaussianFiniteLinearForm (a i) x| ≤ R := by
    simpa [R] using gaussianFiniteLinearForm_abs_le a hcoeff i x
  have htermlo (i : Fin m) :
      Real.exp (-β * R) ≤ Real.exp (β * gaussianFiniteLinearForm (a i) x) := by
    apply Real.exp_le_exp.mpr
    have h := (abs_le.mp (hlin i)).1
    nlinarith [hβ.le]
  have htermhi (i : Fin m) :
      Real.exp (β * gaussianFiniteLinearForm (a i) x) ≤ Real.exp (β * R) := by
    apply Real.exp_le_exp.mpr
    have h := (abs_le.mp (hlin i)).2
    nlinarith [hβ.le]
  let i₀ : Fin m := ⟨0, hm⟩
  have hsumlo : Real.exp (-β * R) ≤ gaussianFiniteLogSumExpDenom β a x := by
    change Real.exp (-β * R) ≤
      ∑ i : Fin m, Real.exp (β * gaussianFiniteLinearForm (a i) x)
    exact (htermlo i₀).trans (Finset.single_le_sum
      (f := fun i : Fin m => Real.exp (β * gaussianFiniteLinearForm (a i) x))
      (fun i hi => (Real.exp_pos _).le) (Finset.mem_univ i₀))
  have hsumhi : gaussianFiniteLogSumExpDenom β a x ≤ (m : ℝ) * Real.exp (β * R) := by
    change (∑ i : Fin m, Real.exp (β * gaussianFiniteLinearForm (a i) x)) ≤ _
    calc
      _ ≤ ∑ _i : Fin m, Real.exp (β * R) := by
        apply Finset.sum_le_sum
        intro i hi
        exact htermhi i
      _ = (m : ℝ) * Real.exp (β * R) := by simp [Finset.sum_const]
  have hDpos : 0 < gaussianFiniteLogSumExpDenom β a x :=
    gaussianFiniteLogSumExp_denominator_pos hm β a x
  have hloglo : -β * R ≤ Real.log (gaussianFiniteLogSumExpDenom β a x) := by
    calc
      -β * R = Real.log (Real.exp (-β * R)) := by rw [Real.log_exp]
      _ ≤ Real.log (gaussianFiniteLogSumExpDenom β a x) :=
        Real.log_le_log (Real.exp_pos _) hsumlo
  have hloghi : Real.log (gaussianFiniteLogSumExpDenom β a x) ≤
      Real.log (m : ℝ) + β * R := by
    calc
      _ ≤ Real.log ((m : ℝ) * Real.exp (β * R)) :=
        Real.log_le_log hDpos hsumhi
      _ = Real.log (m : ℝ) + β * R := by
        rw [Real.log_mul (by exact_mod_cast hm.ne') (Real.exp_ne_zero _), Real.log_exp]
  have hmcast : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm.ne')
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmcast
  have hlogabs : |Real.log (gaussianFiniteLogSumExpDenom β a x)| ≤
      Real.log (m : ℝ) + β * R := by
    apply abs_le.mpr
    constructor <;> linarith [hloglo, hloghi, hlogm, mul_nonneg hβ.le hR]
  change |Real.log (gaussianFiniteLogSumExpDenom β a x) / β| ≤ _
  calc
    |Real.log (gaussianFiniteLogSumExpDenom β a x) / β| =
        |Real.log (gaussianFiniteLogSumExpDenom β a x)| / β := by
      rw [abs_div, abs_of_pos hβ]
    _ ≤ (Real.log (m : ℝ) + β * R) / β :=
      div_le_div_of_nonneg_right hlogabs hβ.le
    _ = Real.log (m : ℝ) / β + R := by
      rw [add_div, mul_div_cancel_left₀ R hβ.ne']
    _ = Real.log (m : ℝ) / β + (n : ℝ) * L * ‖x‖ := by rfl

private theorem gaussianFiniteSoftmaxWeight_le_one {m n : ℕ} (hm : 0 < m)
    (β : ℝ) (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) (i : Fin m) :
    gaussianFiniteSoftmaxWeight β a i x ≤ 1 := by
  have hsum := gaussianFiniteSoftmaxWeight_sum_eq_one hm β a x
  have hle : gaussianFiniteSoftmaxWeight β a i x ≤
      ∑ j : Fin m, gaussianFiniteSoftmaxWeight β a j x :=
    Finset.single_le_sum (fun j hj => gaussianFiniteSoftmaxWeight_nonneg hm β a j x)
      (Finset.mem_univ i)
  rw [hsum] at hle
  exact hle

private theorem abs_gaussianFiniteSoftmaxWeightedSum_le {m n : ℕ} (hm : 0 < m)
    (β : ℝ) (a : Fin m → Fin n → ℝ) (x : Fin n → ℝ) {L : ℝ}
    (c : Fin m → ℝ) (hc : ∀ i, |c i| ≤ L) :
    |∑ i : Fin m, gaussianFiniteSoftmaxWeight β a i x * c i| ≤ L := by
  calc
    |∑ i : Fin m, gaussianFiniteSoftmaxWeight β a i x * c i| ≤
        ∑ i : Fin m, |gaussianFiniteSoftmaxWeight β a i x * c i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin m, gaussianFiniteSoftmaxWeight β a i x * |c i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (gaussianFiniteSoftmaxWeight_nonneg hm β a i x)]
    _ ≤ ∑ i : Fin m, gaussianFiniteSoftmaxWeight β a i x * L := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hc i)
        (gaussianFiniteSoftmaxWeight_nonneg hm β a i x)
    _ = L := by
      rw [← Finset.sum_mul, gaussianFiniteSoftmaxWeight_sum_eq_one hm β a x]
      ring

private theorem abs_coordinateDerivative_gaussianFiniteSoftmaxWeight_le {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : 0 < β) (a : Fin m → Fin n → ℝ)
    (i : Fin m) (k : Fin n) (x : Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) :
    |coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k x| ≤
      2 * β * L * gaussianFiniteSoftmaxWeight β a i x := by
  have hq : |coordinateDerivative (gaussianFiniteLogSumExp β a) k x| ≤ L := by
    rw [coordinateDerivative_gaussianFiniteLogSumExp hm β hβ.ne' a k x]
    exact abs_gaussianFiniteSoftmaxWeightedSum_le hm β a x (fun j => a j k)
      (fun j => gaussianFiniteLinearForm_coordinate_abs_le a hcoeff j k)
  have hqsum := hq
  rw [coordinateDerivative_gaussianFiniteLogSumExp hm β hβ.ne' a k x] at hqsum
  have hai : |a i k| ≤ L := gaussianFiniteLinearForm_coordinate_abs_le a hcoeff i k
  have hpi : 0 ≤ gaussianFiniteSoftmaxWeight β a i x :=
    gaussianFiniteSoftmaxWeight_nonneg hm β a i x
  rw [coordinateDerivative_gaussianFiniteSoftmaxWeight hm β a i k x]
  calc
    |β * gaussianFiniteSoftmaxWeight β a i x *
        (a i k - ∑ j : Fin m, gaussianFiniteSoftmaxWeight β a j x * a j k)| =
      β * gaussianFiniteSoftmaxWeight β a i x *
        |a i k - ∑ j : Fin m, gaussianFiniteSoftmaxWeight β a j x * a j k| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hβ.le, abs_of_nonneg hpi]
    _ ≤ β * gaussianFiniteSoftmaxWeight β a i x *
        (|a i k| + |∑ j : Fin m, gaussianFiniteSoftmaxWeight β a j x * a j k|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (by positivity)
    _ ≤ β * gaussianFiniteSoftmaxWeight β a i x * (L + L) :=
      mul_le_mul_of_nonneg_left (add_le_add hai hqsum) (by positivity)
    _ = 2 * β * L * gaussianFiniteSoftmaxWeight β a i x := by ring

private theorem abs_coordinateDerivative_gaussianFiniteLogSumExp_second_le {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : 0 < β) (a : Fin m → Fin n → ℝ)
    (j k : Fin n) (x : Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) :
    |coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) j) k x| ≤
      2 * β * L ^ 2 := by
  have hL : 0 ≤ L := (norm_nonneg (WithLp.toLp 2 (a ⟨0, hm⟩))).trans (hcoeff ⟨0, hm⟩)
  rw [coordinateDerivative_gaussianFiniteLogSumExp_second hm β hβ.ne' a j k x]
  calc
    |∑ i : Fin m,
        coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k x * a i j| ≤
      ∑ i : Fin m,
        |coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k x * a i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin m,
        |coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k x| * |a i j| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul]
    _ ≤ ∑ i : Fin m,
        (2 * β * L * gaussianFiniteSoftmaxWeight β a i x) * L := by
      apply Finset.sum_le_sum
      intro i hi
      have hpi : 0 ≤ gaussianFiniteSoftmaxWeight β a i x :=
        gaussianFiniteSoftmaxWeight_nonneg hm β a i x
      have hupper : 0 ≤ 2 * β * L * gaussianFiniteSoftmaxWeight β a i x := by
        positivity
      exact mul_le_mul (abs_coordinateDerivative_gaussianFiniteSoftmaxWeight_le
        hm β hβ a i k x hcoeff) (gaussianFiniteLinearForm_coordinate_abs_le a hcoeff i j)
        (abs_nonneg _) hupper
    _ = 2 * β * L ^ 2 := by
      calc
        _ = ∑ i : Fin m, (2 * β * L ^ 2) * gaussianFiniteSoftmaxWeight β a i x := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (2 * β * L ^ 2) *
            ∑ i : Fin m, gaussianFiniteSoftmaxWeight β a i x := by
          rw [Finset.mul_sum]
        _ = 2 * β * L ^ 2 := by
          rw [gaussianFiniteSoftmaxWeight_sum_eq_one hm β a x]
          ring

private theorem abs_coordinateDerivative_gaussianFiniteSoftmaxWeight_second_le {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : 0 < β) (a : Fin m → Fin n → ℝ)
    (i : Fin m) (k l : Fin n) (x : Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) :
    |coordinateDerivative
      (coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k) l x| ≤
      6 * β ^ 2 * L ^ 2 := by
  have hL : 0 ≤ L := (norm_nonneg (WithLp.toLp 2 (a ⟨0, hm⟩))).trans (hcoeff ⟨0, hm⟩)
  have hq : |coordinateDerivative (gaussianFiniteLogSumExp β a) k x| ≤ L := by
    rw [coordinateDerivative_gaussianFiniteLogSumExp hm β hβ.ne' a k x]
    exact abs_gaussianFiniteSoftmaxWeightedSum_le hm β a x (fun j => a j k)
      (fun j => gaussianFiniteLinearForm_coordinate_abs_le a hcoeff j k)
  have hqsecond := abs_coordinateDerivative_gaussianFiniteLogSumExp_second_le
    hm β hβ a k l x hcoeff
  have hp := gaussianFiniteSoftmaxWeight_nonneg hm β a i x
  have hpone := gaussianFiniteSoftmaxWeight_le_one hm β a x i
  have hdp' :
      |coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) l x| ≤ 2 * β * L := by
    calc
      _ ≤ 2 * β * L * gaussianFiniteSoftmaxWeight β a i x :=
        abs_coordinateDerivative_gaussianFiniteSoftmaxWeight_le hm β hβ a i l x hcoeff
      _ ≤ 2 * β * L * 1 :=
        mul_le_mul_of_nonneg_left hpone (by positivity)
      _ = 2 * β * L := by ring
  have hai : |a i k| ≤ L := gaussianFiniteLinearForm_coordinate_abs_le a hcoeff i k
  have hdiff : |a i k - coordinateDerivative (gaussianFiniteLogSumExp β a) k x| ≤
      2 * L := by
    calc
      _ ≤ |a i k| + |coordinateDerivative (gaussianFiniteLogSumExp β a) k x| := abs_sub _ _
      _ ≤ L + L := add_le_add hai hq
      _ = 2 * L := by ring
  have hterm₁ :
      |coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) l x| *
        |a i k - coordinateDerivative (gaussianFiniteLogSumExp β a) k x| ≤
      (2 * β * L) * (2 * L) := by
    exact mul_le_mul hdp' hdiff (abs_nonneg _) (by positivity)
  have hterm₂ : gaussianFiniteSoftmaxWeight β a i x *
      |coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) k) l x| ≤
      1 * (2 * β * L ^ 2) := by
    exact mul_le_mul hpone hqsecond (abs_nonneg _) (by positivity)
  have hterm₁abs :
      |coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) l x *
        (a i k - coordinateDerivative (gaussianFiniteLogSumExp β a) k x)| ≤
      (2 * β * L) * (2 * L) := by
    rw [abs_mul]
    exact hterm₁
  have hterm₂abs :
      |gaussianFiniteSoftmaxWeight β a i x *
        coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) k) l x| ≤
      1 * (2 * β * L ^ 2) := by
    rw [abs_mul, abs_of_nonneg hp]
    exact hterm₂
  rw [coordinateDerivative_gaussianFiniteSoftmaxWeight_second hm β hβ.ne' a i k l x]
  calc
    |β * (coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) l x *
        (a i k - coordinateDerivative (gaussianFiniteLogSumExp β a) k x) -
        gaussianFiniteSoftmaxWeight β a i x *
          coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) k) l x)| =
      β * |coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) l x *
        (a i k - coordinateDerivative (gaussianFiniteLogSumExp β a) k x) -
        gaussianFiniteSoftmaxWeight β a i x *
          coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) k) l x| := by
        rw [abs_mul, abs_of_nonneg hβ.le]
    _ ≤ β * (|coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) l x *
        (a i k - coordinateDerivative (gaussianFiniteLogSumExp β a) k x)| +
        |gaussianFiniteSoftmaxWeight β a i x *
          coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) k) l x|) :=
        mul_le_mul_of_nonneg_left (abs_sub _ _) hβ.le
    _ ≤ β * ((2 * β * L) * (2 * L) + 1 * (2 * β * L ^ 2)) := by
        exact mul_le_mul_of_nonneg_left (add_le_add hterm₁abs hterm₂abs) hβ.le
    _ = 6 * β ^ 2 * L ^ 2 := by ring

private theorem abs_coordinateDerivative_gaussianFiniteLogSumExp_third_le {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : 0 < β) (a : Fin m → Fin n → ℝ)
    (j k l : Fin n) (x : Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) :
    |coordinateDerivative
      (coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) j) k) l x| ≤
      6 * (m : ℝ) * β ^ 2 * L ^ 3 := by
  have hL : 0 ≤ L := (norm_nonneg (WithLp.toLp 2 (a ⟨0, hm⟩))).trans (hcoeff ⟨0, hm⟩)
  rw [coordinateDerivative_gaussianFiniteLogSumExp_third hm β hβ.ne' a j k l x]
  calc
    |∑ i : Fin m,
        coordinateDerivative (coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k) l x *
          a i j| ≤
      ∑ i : Fin m,
        |coordinateDerivative (coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k) l x *
          a i j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin m,
        |coordinateDerivative (coordinateDerivative (gaussianFiniteSoftmaxWeight β a i) k) l x| *
          |a i j| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul]
    _ ≤ ∑ _i : Fin m, (6 * β ^ 2 * L ^ 2) * L := by
      apply Finset.sum_le_sum
      intro i hi
      have hupper : 0 ≤ 6 * β ^ 2 * L ^ 2 := by positivity
      exact mul_le_mul
        (abs_coordinateDerivative_gaussianFiniteSoftmaxWeight_second_le
          hm β hβ a i k l x hcoeff)
        (gaussianFiniteLinearForm_coordinate_abs_le a hcoeff i j)
        (abs_nonneg _) hupper
    _ = 6 * (m : ℝ) * β ^ 2 * L ^ 3 := by
      calc
        _ = (Fintype.card (Fin m) : ℝ) * ((6 * β ^ 2 * L ^ 2) * L) := by
          simp [Finset.sum_const]
        _ = 6 * (m : ℝ) * β ^ 2 * L ^ 3 := by simp [pow_succ]; ring

private theorem hasPolynomiallyBoundedThird_gaussianFiniteLogSumExp {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : 0 < β) (a : Fin m → Fin n → ℝ)
    {L : ℝ} (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) :
    HasPolynomiallyBoundedThirdCoordinateDerivatives (gaussianFiniteLogSumExp β a) := by
  have hL : 0 ≤ L := (norm_nonneg (WithLp.toLp 2 (a ⟨0, hm⟩))).trans (hcoeff ⟨0, hm⟩)
  have hmcast : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm.ne')
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmcast
  have hlogdiv : 0 ≤ Real.log (m : ℝ) / β := div_nonneg hlogm hβ.le
  let C : ℝ := 1 + Real.log (m : ℝ) / β + (n : ℝ) * L + L +
    2 * β * L ^ 2 + 6 * (m : ℝ) * β ^ 2 * L ^ 3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hnL : 0 ≤ (n : ℝ) * L := by positivity
  have hB2 : 0 ≤ 2 * β * L ^ 2 := by positivity
  have hB3 : 0 ≤ 6 * (m : ℝ) * β ^ 2 * L ^ 3 := by positivity
  have hCL : L ≤ C := by dsimp [C]; linarith [hlogdiv, hnL, hB2, hB3]
  have hC2 : 2 * β * L ^ 2 ≤ C := by dsimp [C]; linarith [hlogdiv, hnL, hL, hB3]
  have hC3 : 6 * (m : ℝ) * β ^ 2 * L ^ 3 ≤ C := by
    dsimp [C]
    linarith [hlogdiv, hnL, hL, hB2]
  have hCA : Real.log (m : ℝ) / β + (n : ℝ) * L ≤ C := by
    dsimp [C]
    linarith [hlogdiv, hL, hB2, hB3]
  refine ⟨contDiff_gaussianFiniteLogSumExp hm β a, ⟨C, hC, 1, ?_, ?_, ?_, ?_⟩⟩
  · intro x
    simp only [pow_one]
    have hv := abs_gaussianFiniteLogSumExp_le_linear hm β hβ a x hcoeff
    have hn : 0 ≤ ‖x‖ := norm_nonneg _
    have hnl : 0 ≤ (n : ℝ) * L := by positivity
    calc
      |gaussianFiniteLogSumExp β a x| ≤
          Real.log (m : ℝ) / β + (n : ℝ) * L * ‖x‖ := hv
      _ ≤ (Real.log (m : ℝ) / β + (n : ℝ) * L) * (1 + ‖x‖) := by
        have hcross : 0 ≤ (Real.log (m : ℝ) / β) * ‖x‖ := mul_nonneg hlogdiv hn
        nlinarith [hcross, hnl]
      _ ≤ C * (1 + ‖x‖) :=
        mul_le_mul_of_nonneg_right hCA (by positivity)
  · intro i x
    simp only [pow_one]
    have hfirst : |coordinateDerivative (gaussianFiniteLogSumExp β a) i x| ≤ L := by
      rw [coordinateDerivative_gaussianFiniteLogSumExp hm β hβ.ne' a i x]
      exact abs_gaussianFiniteSoftmaxWeightedSum_le hm β a x (fun j => a j i)
        (fun j => gaussianFiniteLinearForm_coordinate_abs_le a hcoeff j i)
    calc
      |coordinateDerivative (gaussianFiniteLogSumExp β a) i x| ≤ L := hfirst
      _ ≤ C := hCL
      _ ≤ C * (1 + ‖x‖) := by
        calc
          C = C * 1 := by ring
          _ ≤ C * (1 + ‖x‖) :=
            mul_le_mul_of_nonneg_left (by linarith [norm_nonneg x]) hC
  · intro i j x
    simp only [pow_one]
    have hsecond := abs_coordinateDerivative_gaussianFiniteLogSumExp_second_le
      hm β hβ a i j x hcoeff
    calc
      |coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) i) j x| ≤
          2 * β * L ^ 2 := hsecond
      _ ≤ C := hC2
      _ ≤ C * (1 + ‖x‖) :=
        calc
          C = C * 1 := by ring
          _ ≤ C * (1 + ‖x‖) :=
            mul_le_mul_of_nonneg_left (by linarith [norm_nonneg x]) hC
  · intro i j k x
    simp only [pow_one]
    have hthird := abs_coordinateDerivative_gaussianFiniteLogSumExp_third_le
      hm β hβ a i j k x hcoeff
    calc
      |coordinateDerivative
          (coordinateDerivative (coordinateDerivative (gaussianFiniteLogSumExp β a) i) j) k x| ≤
          6 * (m : ℝ) * β ^ 2 * L ^ 3 := hthird
      _ ≤ C := hC3
      _ ≤ C * (1 + ‖x‖) :=
        calc
          C = C * 1 := by ring
          _ ≤ C * (1 + ‖x‖) :=
            mul_le_mul_of_nonneg_left (by linarith [norm_nonneg x]) hC

/-- Log-sum-exp approximates the maximum with its standard dimension-free error. -/
theorem abs_gaussianFiniteLogSumExp_sub_gaussianFiniteMaximum_le {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : 0 < β) (a : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) :
    |gaussianFiniteLogSumExp β a x - gaussianFiniteMaximum hm a x| ≤
      Real.log (m : ℝ) / β := by
  let Hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  let f : Fin m → ℝ := fun i => gaussianFiniteLinearForm (a i) x
  let M : ℝ := (Finset.univ : Finset (Fin m)).sup' Hne f
  let S : ℝ := ∑ i : Fin m, Real.exp (β * f i)
  have hM : M = gaussianFiniteMaximum hm a x := rfl
  have hmaxi (i : Fin m) : f i ≤ M := by
    exact Finset.le_sup' f (Finset.mem_univ i)
  obtain ⟨imax, himax, hmax⟩ := Finset.exists_mem_eq_sup' Hne f
  have hsumlo : Real.exp (β * M) ≤ S := by
    change Real.exp (β * (Finset.univ.sup' Hne f)) ≤
      ∑ i : Fin m, Real.exp (β * f i)
    calc
      Real.exp (β * (Finset.univ.sup' Hne f)) = Real.exp (β * f imax) := by
        exact congrArg (fun y : ℝ => Real.exp (β * y)) hmax
      _ ≤ ∑ i : Fin m, Real.exp (β * f i) :=
        Finset.single_le_sum (f := fun i : Fin m => Real.exp (β * f i))
          (fun i hi => (Real.exp_pos _).le) himax
  have hsumhi : S ≤ (m : ℝ) * Real.exp (β * M) := by
    dsimp [S]
    calc
      _ ≤ ∑ _i : Fin m, Real.exp (β * M) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hmaxi i) hβ.le)
      _ = (m : ℝ) * Real.exp (β * M) := by simp [Finset.sum_const]
  have hSpos : 0 < S := by
    dsimp [S]
    apply Finset.sum_pos'
    · intro i hi
      exact (Real.exp_pos _).le
    · exact ⟨⟨0, hm⟩, Finset.mem_univ _, Real.exp_pos _⟩
  have hloglo : β * M ≤ Real.log S := by
    calc
      β * M = Real.log (Real.exp (β * M)) := by rw [Real.log_exp]
      _ ≤ Real.log S := Real.log_le_log (Real.exp_pos _) hsumlo
  have hloghi : Real.log S ≤ Real.log (m : ℝ) + β * M := by
    calc
      _ ≤ Real.log ((m : ℝ) * Real.exp (β * M)) :=
        Real.log_le_log hSpos hsumhi
      _ = Real.log (m : ℝ) + β * M := by
        rw [Real.log_mul (by exact_mod_cast hm.ne') (Real.exp_ne_zero _), Real.log_exp]
  have hmcast : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm.ne')
  have hlogm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmcast
  have hlow : M ≤ Real.log S / β := (le_div_iff₀ hβ).2 (by nlinarith [hloglo])
  have hhigh : Real.log S / β ≤ M + Real.log (m : ℝ) / β := by
    calc
      _ ≤ (Real.log (m : ℝ) + β * M) / β := div_le_div_of_nonneg_right hloghi hβ.le
      _ = M + Real.log (m : ℝ) / β := by
        rw [add_div, mul_div_cancel_left₀ M hβ.ne']
        ring
  have herror : 0 ≤ Real.log (m : ℝ) / β := div_nonneg hlogm hβ.le
  change |Real.log S / β - M| ≤ Real.log (m : ℝ) / β
  rw [abs_le]
  constructor <;> linarith [hlow, hhigh]

private theorem coordinateGradient_gaussianFiniteLogSumExp_eq {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : β ≠ 0) (a : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) :
    coordinateGradientEuclidean (gaussianFiniteLogSumExp β a) x =
      ∑ i : Fin m, gaussianFiniteSoftmaxWeight β a i x • WithLp.toLp 2 (a i) := by
  ext j
  change coordinateDerivative (gaussianFiniteLogSumExp β a) j x =
    (∑ i : Fin m, gaussianFiniteSoftmaxWeight β a i x • WithLp.toLp 2 (a i)).ofLp j
  rw [coordinateDerivative_gaussianFiniteLogSumExp hm β hβ a j x]
  rw [WithLp.ofLp_sum]
  simp [WithLp.ofLp_smul, Pi.smul_apply]

private theorem norm_coordinateGradient_gaussianFiniteLogSumExp_le {m n : ℕ}
    (hm : 0 < m) (β : ℝ) (hβ : β ≠ 0) (a : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) :
    ‖coordinateGradientEuclidean (gaussianFiniteLogSumExp β a) x‖ ≤ L := by
  rw [coordinateGradient_gaussianFiniteLogSumExp_eq hm β hβ a x]
  calc
    ‖∑ i : Fin m,
        gaussianFiniteSoftmaxWeight β a i x • WithLp.toLp 2 (a i)‖ ≤
      ∑ i : Fin m,
        ‖gaussianFiniteSoftmaxWeight β a i x • WithLp.toLp 2 (a i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin m,
        gaussianFiniteSoftmaxWeight β a i x * ‖WithLp.toLp 2 (a i)‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (gaussianFiniteSoftmaxWeight_nonneg hm β a i x)]
    _ ≤ ∑ i : Fin m, gaussianFiniteSoftmaxWeight β a i x * L := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hcoeff i)
        (gaussianFiniteSoftmaxWeight_nonneg hm β a i x)
    _ = L := by
      rw [← Finset.sum_mul, gaussianFiniteSoftmaxWeight_sum_eq_one hm β a x]
      ring

private theorem continuous_gaussianFiniteMaximum {m n : ℕ} (hm : 0 < m)
    (a : Fin m → Fin n → ℝ) : Continuous (gaussianFiniteMaximum hm a) := by
  let Hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  change Continuous (fun x =>
    (Finset.univ : Finset (Fin m)).sup' Hne
      (fun i => gaussianFiniteLinearForm (a i) x))
  apply continuous_iff_continuousAt.mpr
  intro x
  exact ContinuousAt.finset_sup'_apply (s := Finset.univ) Hne
    (f := fun i y => gaussianFiniteLinearForm (a i) y)
    (fun i hi => (hasFDerivAt_gaussianFiniteLinearForm (a i) x).continuousAt)

private theorem integrable_gaussianFiniteMaximum {m n : ℕ} (hm : 0 < m)
    (a : Fin m → Fin n → ℝ) {L : ℝ}
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) :
    Integrable (gaussianFiniteMaximum hm a) (standardGaussianPi n) := by
  have hL : 0 ≤ L := (norm_nonneg (WithLp.toLp 2 (a ⟨0, hm⟩))).trans (hcoeff ⟨0, hm⟩)
  have hpb := hasPolynomiallyBoundedThird_gaussianFiniteLogSumExp hm 1 zero_lt_one a hcoeff
  have hgrad (x : Fin n → ℝ) :
      ‖coordinateGradientEuclidean (gaussianFiniteLogSumExp 1 a) x‖ ≤ L := by
    exact norm_coordinateGradient_gaussianFiniteLogSumExp_le hm 1 one_ne_zero a x hcoeff
  have hmain := integral_exp_centered_le_of_polynomial_growth
    (L := L) (lam := 0) hpb hL hgrad
  have hFint : Integrable (gaussianFiniteLogSumExp 1 a) (standardGaussianPi n) := hmain.1
  have happrox (x : Fin n → ℝ) :=
    abs_gaussianFiniteLogSumExp_sub_gaussianFiniteMaximum_le hm 1 zero_lt_one a x
  have hdiffMeas : AEStronglyMeasurable
      (fun x => gaussianFiniteMaximum hm a x - gaussianFiniteLogSumExp 1 a x)
      (standardGaussianPi n) :=
    ((continuous_gaussianFiniteMaximum hm a).sub
      (contDiff_gaussianFiniteLogSumExp hm 1 a).continuous).measurable.aestronglyMeasurable
  have hdiff : Integrable
      (fun x => gaussianFiniteMaximum hm a x - gaussianFiniteLogSumExp 1 a x)
      (standardGaussianPi n) := by
    refine Integrable.of_bound hdiffMeas (Real.log (m : ℝ)) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    simpa [abs_sub_comm, div_one] using happrox x
  have hresult : Integrable
      (fun x => (gaussianFiniteMaximum hm a x - gaussianFiniteLogSumExp 1 a x) +
        gaussianFiniteLogSumExp 1 a x) (standardGaussianPi n) := hdiff.add hFint
  convert hresult using 1
  ext x
  ring

private theorem gaussianFiniteMaximum_centered_mgf_slack {m n : ℕ} (hm : 0 < m)
    (a : Fin m → Fin n → ℝ) {L lam β : ℝ} (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L)
    (hβ : 0 < β) :
    Integrable (fun x => Real.exp (lam *
      (gaussianFiniteMaximum hm a x - ∫ y, gaussianFiniteMaximum hm a y ∂(standardGaussianPi n))))
      (standardGaussianPi n) ∧
    (∫ x, Real.exp (lam *
      (gaussianFiniteMaximum hm a x - ∫ y, gaussianFiniteMaximum hm a y ∂(standardGaussianPi n)))
        ∂(standardGaussianPi n)) ≤
      Real.exp (|lam| * (2 * (Real.log (m : ℝ) / β))) *
        Real.exp (lam ^ 2 * L ^ 2 / 2) := by
  let μ : Measure (Fin n → ℝ) := standardGaussianPi n
  let F : (Fin n → ℝ) → ℝ := gaussianFiniteLogSumExp β a
  let mM : ℝ := ∫ x, gaussianFiniteMaximum hm a x ∂μ
  let mF : ℝ := ∫ x, F x ∂μ
  let δ : ℝ := Real.log (m : ℝ) / β
  have hL : 0 ≤ L := (norm_nonneg (WithLp.toLp 2 (a ⟨0, hm⟩))).trans (hcoeff ⟨0, hm⟩)
  have hpb := hasPolynomiallyBoundedThird_gaussianFiniteLogSumExp hm β hβ a hcoeff
  have hgrad (x : Fin n → ℝ) :
      ‖coordinateGradientEuclidean F x‖ ≤ L := by
    exact norm_coordinateGradient_gaussianFiniteLogSumExp_le hm β hβ.ne' a x hcoeff
  have hmain := integral_exp_centered_le_of_polynomial_growth
    (L := L) (lam := lam) hpb hL hgrad
  have hMInt : Integrable (gaussianFiniteMaximum hm a) μ :=
    integrable_gaussianFiniteMaximum hm a hcoeff
  have hFInt : Integrable F μ := by simpa [F] using hmain.1
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    have hmcast : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm.ne')
    exact div_nonneg (Real.log_nonneg hmcast) hβ.le
  have hdiffPoint (x : Fin n → ℝ) :
      ‖gaussianFiniteMaximum hm a x - F x‖ ≤ δ := by
    rw [Real.norm_eq_abs]
    have h := abs_gaussianFiniteLogSumExp_sub_gaussianFiniteMaximum_le hm β hβ a x
    simpa [F, δ, abs_sub_comm] using h
  have hdiffMeas : AEStronglyMeasurable
      (fun x => gaussianFiniteMaximum hm a x - F x) μ := by
    have hcont : Continuous (fun x => gaussianFiniteMaximum hm a x - F x) := by
      exact (continuous_gaussianFiniteMaximum hm a).sub
        (contDiff_gaussianFiniteLogSumExp hm β a).continuous
    exact hcont.measurable.aestronglyMeasurable
  have hdiffInt : Integrable (fun x => gaussianFiniteMaximum hm a x - F x) μ := by
    exact Integrable.of_bound hdiffMeas δ (ae_of_all _ hdiffPoint)
  have hmeanDiff : |mM - mF| ≤ δ := by
    change |(∫ x, gaussianFiniteMaximum hm a x ∂μ) - (∫ x, F x ∂μ)| ≤ δ
    rw [← integral_sub hMInt hFInt]
    calc
      |∫ x, gaussianFiniteMaximum hm a x - F x ∂μ| =
          ‖∫ x, gaussianFiniteMaximum hm a x - F x ∂μ‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∫ x, ‖gaussianFiniteMaximum hm a x - F x‖ ∂μ :=
        norm_integral_le_integral_norm (fun x => gaussianFiniteMaximum hm a x - F x)
      _ ≤ ∫ _x, δ ∂μ :=
        integral_mono_ae hdiffInt.norm (integrable_const δ) (ae_of_all _ hdiffPoint)
      _ = δ := by simp [μ]
  have hcenterDiff (x : Fin n → ℝ) :
      |(gaussianFiniteMaximum hm a x - mM) - (F x - mF)| ≤ 2 * δ := by
    calc
      _ = |(gaussianFiniteMaximum hm a x - F x) - (mM - mF)| := by congr 1; ring
      _ ≤ |gaussianFiniteMaximum hm a x - F x| + |mM - mF| := abs_sub _ _
      _ ≤ δ + δ := add_le_add (by simpa [Real.norm_eq_abs] using hdiffPoint x) hmeanDiff
      _ = 2 * δ := by ring
  have hdomFactor : 0 ≤ Real.exp (|lam| * (2 * δ)) := Real.exp_nonneg _
  have hpoint (x : Fin n → ℝ) :
      Real.exp (lam * (gaussianFiniteMaximum hm a x - mM)) ≤
        Real.exp (|lam| * (2 * δ)) * Real.exp (lam * (F x - mF)) := by
    have hlinear : lam * (gaussianFiniteMaximum hm a x - mM) ≤
        lam * (F x - mF) + |lam| * (2 * δ) := by
      have hmul : lam * ((gaussianFiniteMaximum hm a x - mM) - (F x - mF)) ≤
          |lam| * (2 * δ) := by
        calc
          _ ≤ |lam * ((gaussianFiniteMaximum hm a x - mM) - (F x - mF))| := le_abs_self _
          _ = |lam| * |(gaussianFiniteMaximum hm a x - mM) - (F x - mF)| := abs_mul _ _
          _ ≤ |lam| * (2 * δ) := mul_le_mul_of_nonneg_left (hcenterDiff x) (abs_nonneg _)
      calc
        _ = lam * (F x - mF) +
            lam * ((gaussianFiniteMaximum hm a x - mM) - (F x - mF)) := by ring
        _ = lam * ((gaussianFiniteMaximum hm a x - mM) - (F x - mF)) +
            lam * (F x - mF) := by ring
        _ ≤ |lam| * (2 * δ) + lam * (F x - mF) := add_le_add_left hmul _
        _ = lam * (F x - mF) + |lam| * (2 * δ) := by ring
    calc
      _ ≤ Real.exp (lam * (F x - mF) + |lam| * (2 * δ)) := Real.exp_le_exp.mpr hlinear
      _ = Real.exp (|lam| * (2 * δ)) * Real.exp (lam * (F x - mF)) := by
        rw [Real.exp_add]
        ring
  have hdom : Integrable
      (fun x => Real.exp (|lam| * (2 * δ)) * Real.exp (lam * (F x - mF))) μ := by
    exact hmain.2.2.1.const_mul _
  have hMExpInt : Integrable
      (fun x => Real.exp (lam * (gaussianFiniteMaximum hm a x - mM))) μ := by
    apply hdom.mono_nonneg
    · have hcont : Continuous
        (fun x => Real.exp (lam * (gaussianFiniteMaximum hm a x - mM))) := by
        exact Real.continuous_exp.comp
          (((continuous_gaussianFiniteMaximum hm a).sub continuous_const).const_mul lam)
      exact hcont.measurable.aestronglyMeasurable
    · exact ae_of_all _ (fun x => Real.exp_nonneg _)
    · exact ae_of_all _ hpoint
  have hmainBound :
      (∫ x, Real.exp (lam * (gaussianFiniteMaximum hm a x - mM)) ∂μ) ≤
        Real.exp (|lam| * (2 * δ)) * Real.exp (lam ^ 2 * L ^ 2 / 2) := by
    calc
      _ ≤ ∫ x, Real.exp (|lam| * (2 * δ)) * Real.exp (lam * (F x - mF)) ∂μ :=
        integral_mono_ae hMExpInt hdom (ae_of_all _ hpoint)
      _ = Real.exp (|lam| * (2 * δ)) *
          ∫ x, Real.exp (lam * (F x - mF)) ∂μ := by rw [integral_const_mul]
      _ ≤ Real.exp (|lam| * (2 * δ)) * Real.exp (lam ^ 2 * L ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hmain.2.2.2 hdomFactor
  constructor
  · simpa [μ, mM] using hMExpInt
  · simpa [μ, mM, mF, F, δ] using hmainBound

/-- A finite maximum of linear forms has the sharp Gaussian MGF bound, with the Euclidean
coefficient norm as its Lipschitz constant. The Gaussian measure is the product measure on
`Fin n → ℝ`; gradients are measured in the Euclidean norm. -/
theorem integral_exp_centered_le_of_gaussianFiniteMaximum {m n : ℕ} (hm : 0 < m)
    (a : Fin m → Fin n → ℝ) {L lam : ℝ}
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) :
    Integrable (gaussianFiniteMaximum hm a) (standardGaussianPi n) ∧
    Integrable (fun x => Real.exp (lam * gaussianFiniteMaximum hm a x))
      (standardGaussianPi n) ∧
    Integrable (fun x => Real.exp (lam *
      (gaussianFiniteMaximum hm a x -
        ∫ y, gaussianFiniteMaximum hm a y ∂(standardGaussianPi n)))) (standardGaussianPi n) ∧
    (∫ x, Real.exp (lam *
      (gaussianFiniteMaximum hm a x -
        ∫ y, gaussianFiniteMaximum hm a y ∂(standardGaussianPi n))) ∂(standardGaussianPi n)) ≤
      Real.exp (lam ^ 2 * L ^ 2 / 2) := by
  let μ : Measure (Fin n → ℝ) := standardGaussianPi n
  let mM : ℝ := ∫ x, gaussianFiniteMaximum hm a x ∂μ
  have hL : 0 ≤ L := (norm_nonneg (WithLp.toLp 2 (a ⟨0, hm⟩))).trans (hcoeff ⟨0, hm⟩)
  have hMInt : Integrable (gaussianFiniteMaximum hm a) μ := by
    simpa [μ] using integrable_gaussianFiniteMaximum hm a hcoeff
  have hcenterInt : Integrable
      (fun x => Real.exp (lam * (gaussianFiniteMaximum hm a x - mM))) μ := by
    have h := gaussianFiniteMaximum_centered_mgf_slack hm a hcoeff
      (lam := lam) (β := 1) (by norm_num)
    simpa [μ, mM] using h.1
  have hMrawInt : Integrable
      (fun x => Real.exp (lam * gaussianFiniteMaximum hm a x)) μ := by
    have hscaled : Integrable
        (fun x => Real.exp (lam * mM) * Real.exp (lam *
          (gaussianFiniteMaximum hm a x - mM))) μ := hcenterInt.const_mul _
    have heq : (fun x => Real.exp (lam * gaussianFiniteMaximum hm a x)) =
        (fun x => Real.exp (lam * mM) * Real.exp (lam *
          (gaussianFiniteMaximum hm a x - mM))) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hscaled
  let B : ℝ := Real.exp (lam ^ 2 * L ^ 2 / 2)
  let βseq : ℕ → ℝ := fun N => (N : ℝ) + 1
  let δseq : ℕ → ℝ := fun N => Real.log (m : ℝ) / βseq N
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hβseq : Tendsto βseq atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    have hb := hnat.eventually (eventually_ge_atTop b)
    filter_upwards [hb] with N hN
    dsimp [βseq]
    linarith
  have hinv : Tendsto (fun N => (βseq N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hβseq
  have hδseq : Tendsto δseq atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => Real.log (m : ℝ)) atTop
        (nhds (Real.log (m : ℝ))) := tendsto_const_nhds
    have h := hconst.mul hinv
    simpa [δseq, div_eq_mul_inv] using h
  have htwoδ : Tendsto (fun N => 2 * δseq N) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
    simpa using hconst.mul hδseq
  have harg : Tendsto (fun N => |lam| * (2 * δseq N)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => |lam|) atTop (nhds |lam|) := tendsto_const_nhds
    simpa using hconst.mul htwoδ
  have hfactor : Tendsto (fun N => Real.exp (|lam| * (2 * δseq N))) atTop (nhds 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp harg
    simpa [Function.comp_def] using h
  have hfactorB : Tendsto (fun N => Real.exp (|lam| * (2 * δseq N)) * B)
      atTop (nhds B) := by
    simpa [B] using hfactor.mul_const B
  have hbound (N : ℕ) :
      (∫ x, Real.exp (lam * (gaussianFiniteMaximum hm a x - mM)) ∂μ) ≤
        Real.exp (|lam| * (2 * δseq N)) * B := by
    have h := gaussianFiniteMaximum_centered_mgf_slack hm a hcoeff
      (lam := lam) (β := βseq N) (by dsimp [βseq]; positivity)
    simpa [μ, mM, δseq, B] using h.2
  have hcenterBound :
      (∫ x, Real.exp (lam * (gaussianFiniteMaximum hm a x - mM)) ∂μ) ≤ B :=
    ge_of_tendsto hfactorB (Filter.Eventually.of_forall hbound)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [μ] using hMInt
  · simpa [μ, mM] using hMrawInt
  · simpa [μ, mM] using hcenterInt
  · simpa [μ, mM, B] using hcenterBound

/-- Two-sided sharp Gaussian tails for a finite maximum of linear forms. -/
theorem measure_centered_tail_le_of_gaussianFiniteMaximum {m n : ℕ} (hm : 0 < m)
    (a : Fin m → Fin n → ℝ) {L t : ℝ} (_hL : 0 < L) (ht : 0 ≤ t)
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L) :
    (standardGaussianPi n).real {x | t ≤ gaussianFiniteMaximum hm a x -
      ∫ y, gaussianFiniteMaximum hm a y ∂(standardGaussianPi n)} ≤
        Real.exp (-t ^ 2 / (2 * L ^ 2)) ∧
    (standardGaussianPi n).real {x | gaussianFiniteMaximum hm a x -
      ∫ y, gaussianFiniteMaximum hm a y ∂(standardGaussianPi n) ≤ -t} ≤
        Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
  let X : (Fin n → ℝ) → ℝ := fun x => gaussianFiniteMaximum hm a x -
    ∫ y, gaussianFiniteMaximum hm a y ∂(standardGaussianPi n)
  have hmoment (r : ℝ) := integral_exp_centered_le_of_gaussianFiniteMaximum
    hm a (L := L) (lam := r) hcoeff
  have hcoe : (((L ^ 2).toNNReal : ℝ)) = L ^ 2 :=
    Real.coe_toNNReal _ (sq_nonneg L)
  have hsub : HasSubgaussianMGF X (L ^ 2).toNNReal (standardGaussianPi n) := by
    refine ⟨?_, ?_⟩
    · intro r
      simpa [X] using (hmoment r).2.2.1
    · intro r
      rw [ProbabilityTheory.mgf]
      simpa [X, hcoe, mul_comm, mul_left_comm, mul_assoc] using (hmoment r).2.2.2
  have hright := hsub.measure_ge_le ht
  have hleft := hsub.neg.measure_ge_le ht
  have hset : {x | X x ≤ -t} = {x | t ≤ -X x} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro hx <;> linarith
  refine ⟨?_, ?_⟩
  · simpa [X, hcoe] using hright
  · rw [hset]
    simpa [X, hcoe] using hleft

end ASDExplicitGamma.Gaussian
