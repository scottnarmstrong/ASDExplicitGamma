/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.ConcentrationBridge
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Gaussian heat interpolation moment

This file establishes the growth controls needed to differentiate the outer Gaussian moment.
-/

@[expose] public section

open MeasureTheory
open ProbabilityTheory
open scoped Topology

namespace ASDExplicitGamma.Gaussian

instance standardGaussianPi_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (standardGaussianPi n) := by
  unfold standardGaussianPi
  infer_instance

/-- The vector of coordinate derivatives, given the Euclidean `ℓ²` norm. -/
noncomputable def coordinateGradientEuclidean {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => coordinateDerivative F i x)

private theorem hasPolySecond_from_third_early {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives F := by
  rcases hF₃ with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  exact ⟨hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3),
    ⟨C, hC, d, hzero, hone, htwo⟩⟩

private theorem abs_coordinate_le_euclidean_norm_local {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) : |v i| ≤ ‖v‖ := by
  have hsum : (‖v i‖ : ℝ) ^ 2 ≤ ∑ j : Fin n, (‖v j‖ : ℝ) ^ 2 :=
    Finset.single_le_sum (fun j hj => sq_nonneg (‖v j‖)) (Finset.mem_univ i)
  rw [EuclideanSpace.norm_eq]
  rw [← Real.norm_eq_abs]
  exact (Real.le_sqrt (norm_nonneg (v i)) (by positivity)).2 hsum

theorem norm_coordinateGradient_heatAverage_le {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {L : ℝ}
    (hgrad : ∀ x, ‖coordinateGradientEuclidean F x‖ ≤ L)
    (x : Fin n → ℝ) (t : ℝ) :
    ‖coordinateGradientEuclidean (fun y => heatAverage F y t) x‖ ≤ L := by
  have hF₂ := hasPolySecond_from_third_early hF₃
  let gradF : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) := coordinateGradientEuclidean F
  have hgradCont : Continuous gradF := by
    have hcoords : Continuous (fun x : Fin n → ℝ => fun i => coordinateDerivative F i x) := by
      apply continuous_pi
      intro i
      have hfdcont := hF₃.1.continuous_fderiv (by norm_num)
      unfold coordinateDerivative
      exact hfdcont.clm_apply continuous_const
    dsimp [gradF, coordinateGradientEuclidean]
    exact (PiLp.continuous_toLp 2 _).comp hcoords
  have hgradInt : Integrable (fun ξ : Fin n → ℝ => gradF (x + Real.sqrt t • ξ))
      (standardGaussianPi n) := by
    apply Integrable.of_bound
      (hgradCont.comp (continuous_const.add (continuous_id.const_smul (Real.sqrt t)))).measurable.aestronglyMeasurable
      L
    exact ae_of_all _ fun ξ => by simpa [gradF] using hgrad (x + Real.sqrt t • ξ)
  have hgradEq : coordinateGradientEuclidean (fun y => heatAverage F y t) x =
      ∫ ξ, gradF (x + Real.sqrt t • ξ) ∂(standardGaussianPi n) := by
    ext i
    change coordinateDerivative (fun y => heatAverage F y t) i x =
      (∫ ξ, gradF (x + Real.sqrt t • ξ) ∂(standardGaussianPi n)) i
    rw [coordinateDerivative_heatAverage hF₂ t i x]
    calc
      heatAverage (coordinateDerivative F i) x t =
          ∫ ξ, coordinateDerivative F i (x + Real.sqrt t • ξ)
            ∂(standardGaussianPi n) := rfl
      _ = ∫ ξ, (EuclideanSpace.proj i) (gradF (x + Real.sqrt t • ξ))
            ∂(standardGaussianPi n) := by
          apply integral_congr_ae
          exact ae_of_all _ fun ξ => by simp [gradF, coordinateGradientEuclidean]
      _ = (EuclideanSpace.proj i) (∫ ξ, gradF (x + Real.sqrt t • ξ)
            ∂(standardGaussianPi n)) := (EuclideanSpace.proj i).integral_comp_comm hgradInt
      _ = _ := rfl
  calc
    ‖coordinateGradientEuclidean (fun y => heatAverage F y t) x‖ =
        ‖∫ ξ, gradF (x + Real.sqrt t • ξ) ∂(standardGaussianPi n)‖ :=
      congrArg norm hgradEq
    _ ≤ ∫ ξ, ‖gradF (x + Real.sqrt t • ξ)‖ ∂(standardGaussianPi n) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _ξ, L ∂(standardGaussianPi n) := by
      apply integral_mono_ae hgradInt.norm (integrable_const L)
      exact ae_of_all _ fun ξ => by simpa [gradF] using hgrad (x + Real.sqrt t • ξ)
    _ = L := by simp [standardGaussianPi]

/-- The coordinate square sum is the squared Euclidean norm of the coordinate gradient. -/
theorem sum_sq_coordinateGradient_eq_norm_sq {n : ℕ}
    (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, (coordinateDerivative F i x) ^ 2) =
      ‖coordinateGradientEuclidean F x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [coordinateGradientEuclidean]

private theorem contDiff_coordinateDerivative_c2_local {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 3 F) (i : Fin n) :
    ContDiff ℝ 2 (coordinateDerivative F i) := by
  have h := hF.contDiff_fderiv_apply (m := 2)
    (by norm_num : (2 : WithTop ℕ∞) + 1 ≤ 3)
  have hpair : ContDiff ℝ 2
      (fun x : Fin n → ℝ => (x, (Pi.single i (1 : ℝ) : Fin n → ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hcomp := h.comp hpair
  convert hcomp using 1
  · ext x
    rfl

private theorem contDiff_coordinateDerivative_c1_local {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ 2 F) (i : Fin n) :
    ContDiff ℝ 1 (coordinateDerivative F i) := by
  have h := hF.contDiff_fderiv_apply (m := 1)
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hpair : ContDiff ℝ 1
      (fun x : Fin n → ℝ => (x, (Pi.single i (1 : ℝ) : Fin n → ℝ))) :=
    contDiff_id.prodMk contDiff_const
  have hcomp := h.comp hpair
  convert hcomp using 1
  · ext x
    rfl

private theorem coordinateDerivative_mul_local {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordinateDerivative (fun y => f y * g y) i x =
      coordinateDerivative f i x * g x + f x * coordinateDerivative g i x := by
  let e : Fin n → ℝ := Pi.single i 1
  have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L e) (fderiv_fun_mul hf hg)
  simpa [coordinateDerivative, e, smul_apply, smul_eq_mul, add_comm, add_left_comm,
    add_assoc, mul_comm, mul_left_comm, mul_assoc] using h

private theorem coordinateDerivative_const_mul_local {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x) (c : ℝ)
    (i : Fin n) :
    coordinateDerivative (fun y => c * f y) i x = c * coordinateDerivative f i x := by
  have hmul := coordinateDerivative_mul_local (differentiableAt_const c) hf i
  rw [hmul]
  simp [coordinateDerivative]

private theorem coordinateDerivative_exp_linear_local {n : ℕ}
    {U : (Fin n → ℝ) → ℝ} (hU : ContDiff ℝ 1 U) (lam : ℝ)
    (i : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (fun y => Real.exp (lam * U y)) i x =
      lam * Real.exp (lam * U x) * coordinateDerivative U i x := by
  let e : Fin n → ℝ := Pi.single i 1
  have hUfd : HasFDerivAt U (fderiv ℝ U x) x := (hU.differentiable_one x).hasFDerivAt
  have hinner : HasFDerivAt (fun y => lam * U y) (lam • fderiv ℝ U x) x := by
    convert hUfd.const_mul lam using 1
  have houter := (Real.hasDerivAt_exp (lam * U x)).hasFDerivAt
  have hcomp := houter.comp x hinner
  have h := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L e) hcomp.fderiv
  simpa [Function.comp_def, coordinateDerivative, e, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, mul_comm, mul_left_comm, mul_assoc] using h

private theorem coordinateDerivative_second_exp_linear_local {n : ℕ}
    {U : (Fin n → ℝ) → ℝ} (hU : ContDiff ℝ 2 U) (lam : ℝ)
    (i j : Fin n) (x : Fin n → ℝ) :
    coordinateDerivative (coordinateDerivative
      (fun y => Real.exp (lam * U y)) i) j x =
      lam ^ 2 * Real.exp (lam * U x) * coordinateDerivative U j x *
          coordinateDerivative U i x +
        lam * Real.exp (lam * U x) *
          coordinateDerivative (coordinateDerivative U i) j x := by
  let E : (Fin n → ℝ) → ℝ := fun y => Real.exp (lam * U y)
  let P : (Fin n → ℝ) → ℝ := fun y => lam * E y
  let Q : (Fin n → ℝ) → ℝ := coordinateDerivative U i
  have hU₁ : ContDiff ℝ 1 U := hU.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hscaled₁ : ContDiff ℝ 1 (fun y => lam * U y) := contDiff_const.mul hU₁
  have hE₁ : ContDiff ℝ 1 E := Real.contDiff_exp.comp hscaled₁
  have hP₁ : ContDiff ℝ 1 P := contDiff_const.mul hE₁
  have hfirst : coordinateDerivative (fun y => Real.exp (lam * U y)) i =
      fun y => P y * Q y := by
    funext y
    simp only [P, Q]
    exact coordinateDerivative_exp_linear_local hU₁ (lam := lam) i y
  have hPdiff : DifferentiableAt ℝ P x := hP₁.differentiable_one x
  have hQdiff : DifferentiableAt ℝ Q x := by
    exact (contDiff_coordinateDerivative_c1_local hU i).differentiable_one x
  have hmul := coordinateDerivative_mul_local hPdiff hQdiff j
  rw [hfirst]
  rw [hmul]
  have hPderiv : coordinateDerivative P j x =
      lam * coordinateDerivative E j x := by
    exact coordinateDerivative_const_mul_local (hE₁.differentiable_one x) lam j
  rw [hPderiv, show coordinateDerivative E j x =
      lam * Real.exp (lam * U x) * coordinateDerivative U j x from
        coordinateDerivative_exp_linear_local hU₁ (lam := lam) j x]
  simp only [P, Q]
  dsimp [E]
  ring

private theorem hasPolynomiallyBoundedSecond_exp_linear_local {n : ℕ}
    {U : (Fin n → ℝ) → ℝ} (hU₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives U)
    {B L lam : ℝ} (hL : 0 ≤ L)
    (hUbound : ∀ x, |U x| ≤ B)
    (hgrad : ∀ i x, |coordinateDerivative U i x| ≤ L) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives
      (fun x => Real.exp (lam * U x)) := by
  rcases hU₂.2 with ⟨C, hC, d, hzero, hone, htwo⟩
  let Q : ℝ := Real.exp (|lam| * B)
  let C' : ℝ := Q * (1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hpoly (x : Fin n → ℝ) : 1 ≤ (1 + ‖x‖) ^ d := by
    have hx : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    exact one_le_pow₀ hx
  have hexp (x : Fin n → ℝ) : |Real.exp (lam * U x)| ≤ Q := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      lam * U x ≤ |lam * U x| := le_abs_self _
      _ = |lam| * |U x| := abs_mul _ _
      _ ≤ |lam| * B := mul_le_mul_of_nonneg_left (hUbound x) (abs_nonneg _)
  have hU₁ : ContDiff ℝ 1 U :=
    hU₂.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hcont : ContDiff ℝ 2 (fun x => Real.exp (lam * U x)) := by
    have hscaled : ContDiff ℝ 2 (fun x => lam * U x) := contDiff_const.mul hU₂.1
    exact Real.contDiff_exp.comp hscaled
  refine ⟨hcont, C', hC', d, ?_, ?_, ?_⟩
  · intro x
    calc
      |Real.exp (lam * U x)| ≤ Q := hexp x
      _ ≤ C' * (1 + ‖x‖) ^ d := by
        dsimp [C']
        have hpolyx := hpoly x
        have hfactor : 1 ≤ 1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C := by
          nlinarith [mul_nonneg (abs_nonneg lam) hL,
            mul_nonneg (abs_nonneg lam) hC, sq_nonneg (lam * L)]
        have hfactor0 : 0 ≤ 1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C := by positivity
        have hstep1 : Q ≤ Q *
            (1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C) := by
          nlinarith [mul_le_mul_of_nonneg_left hfactor (le_of_lt hQ)]
        have hstep2 : Q * (1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C) ≤
            Q * (1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C) *
              (1 + ‖x‖) ^ d := by
          nlinarith [mul_nonneg (mul_nonneg (le_of_lt hQ) hfactor0)
            (sub_nonneg.mpr hpolyx)]
        exact hstep1.trans hstep2
  · intro i x
    rw [coordinateDerivative_exp_linear_local hU₁ (lam := lam) i x]
    have hbound := hgrad i x
    calc
      |lam * Real.exp (lam * U x) * coordinateDerivative U i x| ≤
          |lam| * Q * L := by
        rw [abs_mul, abs_mul]
        gcongr
        exact hexp x
      _ ≤ C' * (1 + ‖x‖) ^ d := by
        dsimp [C']
        have hpolyx := hpoly x
        have hfactor : |lam| * L ≤ 1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C := by
          nlinarith [sq_nonneg (lam * L), mul_nonneg hC (abs_nonneg lam)]
        have hQnonneg : 0 ≤ Q := le_of_lt hQ
        have hfirst : |lam| * Q * L ≤ Q *
            (1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C) := by
          calc
            |lam| * Q * L = Q * (|lam| * L) := by ring
            _ ≤ Q * (1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C) :=
              mul_le_mul_of_nonneg_left hfactor hQnonneg
        calc
          |lam| * Q * L ≤ Q *
              (1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C) := hfirst
          _ ≤ Q * (1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C) *
              (1 + ‖x‖) ^ d := by
            have hprod : 0 ≤ Q * (1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C) := by
              positivity
            nlinarith [mul_nonneg hprod (sub_nonneg.mpr hpolyx)]
  · intro i j x
    rw [coordinateDerivative_second_exp_linear_local hU₂.1 (lam := lam) i j x]
    have hpolyx := hpoly x
    have hD1 : |coordinateDerivative U j x| ≤ L := hgrad j x
    have hD2 : |coordinateDerivative U i x| ≤ L := hgrad i x
    have hDij : |coordinateDerivative (coordinateDerivative U i) j x| ≤
        C * (1 + ‖x‖) ^ d := htwo i j x
    have hfirst : |lam ^ 2 * Real.exp (lam * U x) *
        coordinateDerivative U j x * coordinateDerivative U i x| ≤
        Q * (lam ^ 2 * L ^ 2) := by
      rw [abs_mul, abs_mul, abs_mul]
      calc
        |lam ^ 2| * |Real.exp (lam * U x)| *
            |coordinateDerivative U j x| * |coordinateDerivative U i x| ≤
            |lam ^ 2| * Q * L * L := by
              gcongr
              exact hexp x
        _ = Q * (lam ^ 2 * L ^ 2) := by rw [abs_of_nonneg (sq_nonneg lam)]; ring
    have hsecond : |lam * Real.exp (lam * U x) *
        coordinateDerivative (coordinateDerivative U i) j x| ≤
        Q * (|lam| * C) * (1 + ‖x‖) ^ d := by
      rw [abs_mul, abs_mul]
      calc
        |lam| * |Real.exp (lam * U x)| *
            |coordinateDerivative (coordinateDerivative U i) j x| ≤
            |lam| * Q * (C * (1 + ‖x‖) ^ d) := by
              gcongr
              exact hexp x
        _ = Q * (|lam| * C) * (1 + ‖x‖) ^ d := by ring
    calc
      |lam ^ 2 * Real.exp (lam * U x) * coordinateDerivative U j x *
          coordinateDerivative U i x + lam * Real.exp (lam * U x) *
          coordinateDerivative (coordinateDerivative U i) j x| ≤
          Q * (lam ^ 2 * L ^ 2) +
            Q * (|lam| * C) * (1 + ‖x‖) ^ d :=
        (abs_add_le _ _).trans (add_le_add hfirst hsecond)
      _ ≤ C' * (1 + ‖x‖) ^ d := by
        dsimp [C']
        have hfactor : lam ^ 2 * L ^ 2 + |lam| * C ≤
            1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C := by
          nlinarith [mul_nonneg (abs_nonneg lam) hL]
        have hQnonneg : 0 ≤ Q := le_of_lt hQ
        have hpolyNonneg : 0 ≤ (1 + ‖x‖) ^ d := by positivity
        calc
          Q * (lam ^ 2 * L ^ 2) + Q * (|lam| * C) * (1 + ‖x‖) ^ d ≤
              Q * (lam ^ 2 * L ^ 2 + |lam| * C) * (1 + ‖x‖) ^ d := by
            have hA : 0 ≤ Q * (lam ^ 2 * L ^ 2) := by positivity
            nlinarith [mul_nonneg hA (sub_nonneg.mpr hpolyx)]
          _ ≤ Q * (1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C) *
              (1 + ‖x‖) ^ d := by
            gcongr
          _ = Q * (1 + |lam| * L + lam ^ 2 * L ^ 2 + |lam| * C) *
              (1 + ‖x‖) ^ d := rfl

private theorem hasPolynomiallyBoundedSecond_of_third_moment {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives F := by
  rcases hF₃ with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  exact ⟨hcont.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3),
    ⟨C, hC, d, hzero, hone, htwo⟩⟩

private theorem abs_coordinateDerivative_heatAverage_le_local {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {L : ℝ} (hL : 0 ≤ L)
    (hgrad : ∀ i x, |coordinateDerivative F i x| ≤ L)
    (i : Fin n) (x : Fin n → ℝ) (t : ℝ) :
    |coordinateDerivative (fun y => heatAverage F y t) i x| ≤ L := by
  have hF₂ := hasPolynomiallyBoundedSecond_of_third_moment hF₃
  rcases hF₃ with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  rw [coordinateDerivative_heatAverage hF₂ t i x]
  have hcoord : ∀ z, |coordinateDerivative F i z| ≤ L * (1 + ‖z‖) ^ 0 := by
    intro z
    simpa using hgrad i z
  have hbound := abs_shiftAverage_le_of_polynomial_bound
    (contDiff_coordinateDerivative_c2_local hcont i).continuous hL hcoord x (Real.sqrt t)
  have hmass : (standardGaussianPi n).real Set.univ = 1 := by
    simp [standardGaussianPi]
  simpa [heatAverage, shiftAverage, hmass] using hbound

private theorem abs_heatAverage_le_of_bounded_local {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {B : ℝ} (hB : 0 ≤ B) (hFbound : ∀ x, |F x| ≤ B)
    (x : Fin n → ℝ) (t : ℝ) : |heatAverage F x t| ≤ B := by
  rcases hF₃ with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  have hbounded : ∀ z, |F z| ≤ B * (1 + ‖z‖) ^ 0 := by
    intro z
    simpa using hFbound z
  have hbound := abs_shiftAverage_le_of_polynomial_bound hcont.continuous hB hbounded x
    (Real.sqrt t)
  have hmass : (standardGaussianPi n).real Set.univ = 1 := by
    simp [standardGaussianPi]
  simpa [heatAverage, shiftAverage, hmass] using hbound

/-- For a `C³` function, the spatial Laplacian of its Gaussian heat average is continuous. -/
theorem continuous_heatLaplacianAverage_of_third {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F) (t : ℝ) :
    Continuous (fun x : Fin n → ℝ => heatLaplacianAverage F x t) := by
  rcases hF₃ with ⟨hFcont, C, hC, d, hzero, hone, htwo, hthree⟩
  let H : (Fin n → ℝ) → ℝ := fun x =>
    ∑ i : Fin n, coordinateDerivative (coordinateDerivative F i) i x
  let C₀ : ℝ := (Fintype.card (Fin n) : ℝ) * C
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hHcont : Continuous H := by
    apply continuous_finsetSum
    intro i hi
    exact (contDiff_coordinateDerivative_c1_local
      (contDiff_coordinateDerivative_c2_local hFcont i) i).continuous
  have hHbound : ∀ x, |H x| ≤ C₀ * (1 + ‖x‖) ^ d := by
    intro x
    calc
      |H x| ≤ ∑ i : Fin n,
          |coordinateDerivative (coordinateDerivative F i) i x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, C * (1 + ‖x‖) ^ d := by
        apply Finset.sum_le_sum
        intro i hi
        exact htwo i i x
      _ = C₀ * (1 + ‖x‖) ^ d := by
        simp [C₀, Finset.sum_const, nsmul_eq_mul]
        ring
  apply continuous_iff_continuousAt.mpr
  intro x
  have hcenter := continuousAt_shiftAverage_center_of_polynomial_bound hHcont hC₀
    hHbound x (Real.sqrt t)
  simpa [heatLaplacianAverage, H, shiftAverage] using hcenter

private noncomputable def gaussianHeatMomentIntegrand {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (lam r : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  Real.exp (lam * heatAverage F (Real.sqrt r • ξ) (1 - r))

private noncomputable def gaussianHeatMomentBridgeDerivative {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (r : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  fderiv ℝ (fun x => heatAverage F x (1 - r)) (Real.sqrt r • ξ) ξ /
      (2 * Real.sqrt r) -
    (1 / 2 : ℝ) * heatLaplacianAverage F (Real.sqrt r • ξ) (1 - r)

private noncomputable def gaussianHeatMomentIntegrandDerivative {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (lam r : ℝ) (ξ : Fin n → ℝ) : ℝ :=
  lam * gaussianHeatMomentIntegrand F lam r ξ *
    gaussianHeatMomentBridgeDerivative F r ξ

private lemma hasDerivAt_gaussian_heatMoment_integrand {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    (lam : ℝ) (ξ : Fin n → ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun s => gaussianHeatMomentIntegrand F lam s ξ)
      (gaussianHeatMomentIntegrandDerivative F lam r ξ) r := by
  have hbridge := hasDerivAt_gaussian_heatBridge hF₃ ξ hr hr1
  have hscaled : HasDerivAt
      (fun s => lam * heatAverage F (Real.sqrt s • ξ) (1 - s))
      (lam * gaussianHeatMomentBridgeDerivative F r ξ) r := by
    simpa [gaussianHeatMomentBridgeDerivative, mul_comm] using hbridge.const_mul lam
  have hexp := (Real.hasDerivAt_exp
    (lam * heatAverage F (Real.sqrt r • ξ) (1 - r))).comp r hscaled
  simpa [gaussianHeatMomentIntegrand, gaussianHeatMomentIntegrandDerivative,
    Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hexp

private theorem abs_heatLaplacianAverage_le_of_third_local {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ (x : Fin n → ℝ) (t : ℝ),
      0 ≤ t → t ≤ 1 →
        |heatLaplacianAverage F x t| ≤ C * (1 + ‖x‖) ^ d := by
  rcases hF₃ with ⟨hFcont, C, hC, d, hzero, hone, htwo, hthree⟩
  let H : (Fin n → ℝ) → ℝ := fun x =>
    ∑ i : Fin n, coordinateDerivative (coordinateDerivative F i) i x
  let C₀ : ℝ := (Fintype.card (Fin n) : ℝ) * C
  let M : ℝ := ∫ ξ, (1 + ‖ξ‖) ^ d ∂(standardGaussianPi n)
  let C₁ : ℝ := C₀ * 2 ^ d * M
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hM : 0 ≤ M := by
    apply integral_nonneg
    intro ξ
    positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hHcont : Continuous H := by
    apply continuous_finsetSum
    intro i hi
    exact (contDiff_coordinateDerivative_c1_local
      (contDiff_coordinateDerivative_c2_local hFcont i) i).continuous
  have hHbound : ∀ x, |H x| ≤ C₀ * (1 + ‖x‖) ^ d := by
    intro x
    calc
      |H x| ≤ ∑ i : Fin n,
          |coordinateDerivative (coordinateDerivative F i) i x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, C * (1 + ‖x‖) ^ d := by
        apply Finset.sum_le_sum
        intro i hi
        exact htwo i i x
      _ = C₀ * (1 + ‖x‖) ^ d := by
        simp [C₀, Finset.sum_const, nsmul_eq_mul]
        ring
  refine ⟨C₁, hC₁, d, ?_⟩
  intro x t ht0 ht1
  let c : ℝ := Real.sqrt t
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc1 : c ≤ 1 := by
    dsimp [c]
    rw [Real.sqrt_le_one]
    exact ht1
  have hca : |c| ≤ 1 := by simpa [abs_of_nonneg hc0] using hc1
  have hshift := abs_shiftAverage_le_of_polynomial_bound hHcont hC₀ hHbound x c
  have hfactor : (1 + |c|) ^ d ≤ 2 ^ d := by
    gcongr
    linarith [hca]
  have hbound := calc
    |shiftAverage H x c| ≤
        (C₀ * (1 + |c|) ^ d * M) * (1 + ‖x‖) ^ d := hshift
    _ ≤ (C₀ * 2 ^ d * M) * (1 + ‖x‖) ^ d := by gcongr
  simpa [heatLaplacianAverage, H, shiftAverage, c, M, C₀, C₁] using hbound

private lemma abs_gaussianHeatMomentIntegrand_le_of_bounded {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {B : ℝ} (hB : 0 ≤ B) (hFbound : ∀ x, |F x| ≤ B)
    (lam r : ℝ) (ξ : Fin n → ℝ) :
    |gaussianHeatMomentIntegrand F lam r ξ| ≤ Real.exp (|lam| * B) := by
  rw [gaussianHeatMomentIntegrand, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    lam * heatAverage F (Real.sqrt r • ξ) (1 - r) ≤
        |lam * heatAverage F (Real.sqrt r • ξ) (1 - r)| := le_abs_self _
    _ = |lam| * |heatAverage F (Real.sqrt r • ξ) (1 - r)| := abs_mul _ _
    _ ≤ |lam| * B := by
      gcongr
      exact abs_heatAverage_le_of_bounded_local hF₃ hB hFbound _ _

/-- Exponentials of heat averages of a bounded function have a uniform integrable bound. -/
theorem abs_exp_heatAverage_le_of_bounded {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {B : ℝ} (hB : 0 ≤ B) (hFbound : ∀ x, |F x| ≤ B)
    (lam r : ℝ) (x : Fin n → ℝ) :
    |Real.exp (lam * heatAverage F x r)| ≤ Real.exp (|lam| * B) := by
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    lam * heatAverage F x r ≤ |lam * heatAverage F x r| := le_abs_self _
    _ = |lam| * |heatAverage F x r| := abs_mul _ _
    _ ≤ |lam| * B := by
      gcongr
      exact abs_heatAverage_le_of_bounded_local hF₃ hB hFbound x r

private lemma moment_norm_add_smul_bound {n : ℕ}
    (x ξ : Fin n → ℝ) (c : ℝ) :
    1 + ‖x + c • ξ‖ ≤ (1 + ‖x‖) * (1 + |c|) * (1 + ‖ξ‖) := by
  have htri : ‖x + c • ξ‖ ≤ ‖x‖ + |c| * ‖ξ‖ := by
    calc
      ‖x + c • ξ‖ ≤ ‖x‖ + ‖c • ξ‖ := norm_add_le _ _
      _ = ‖x‖ + |c| * ‖ξ‖ := by simp [norm_smul]
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have hc : 0 ≤ |c| := abs_nonneg _
  have hξ : 0 ≤ ‖ξ‖ := norm_nonneg _
  nlinarith [mul_nonneg hx hc, mul_nonneg hx hξ, mul_nonneg hc hξ]

private theorem integrable_shift_poly_moment {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) {d : ℕ}
    (hg : ∀ z, |f z| ≤ C * (1 + ‖z‖) ^ d)
    (x : Fin n → ℝ) (c : ℝ) :
    Integrable (fun ξ => f (x + c • ξ)) (standardGaussianPi n) := by
  let B : ℝ := (1 + ‖x‖) * (1 + |c|)
  let K : ℝ := C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmeas : Measurable (fun ξ : Fin n → ℝ => f (x + c • ξ)) :=
    (hf.comp (continuous_const.add (continuous_id.const_smul c))).measurable
  have hbound : ∀ ξ, |f (x + c • ξ)| ≤ K * (1 + ‖ξ‖) ^ d := by
    intro ξ
    calc
      |f (x + c • ξ)| ≤ C * (1 + ‖x + c • ξ‖) ^ d := hg _
      _ ≤ C * (B * (1 + ‖ξ‖)) ^ d := by
        gcongr
        exact moment_norm_add_smul_bound x ξ c
      _ = K * (1 + ‖ξ‖) ^ d := by dsimp [B, K]; rw [mul_pow]; ring
  apply integrable_of_pi_polynomial_bound hmeas hK (d := d)
  intro ξ
  simpa [Real.norm_eq_abs] using hbound ξ

private theorem hasPolySecond_coordinateDerivative_moment {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F) (i : Fin n) :
    HasPolynomiallyBoundedSecondCoordinateDerivatives (coordinateDerivative F i) := by
  rcases hF₃ with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  exact ⟨contDiff_coordinateDerivative_c2_local hcont i, C, hC, d,
    hone i, htwo i, hthree i⟩

/-- The Laplacian of a Gaussian heat average is the heat average of the Laplacian. -/
theorem heatLaplacianAverage_eq_trace_heatAverage {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    (x : Fin n → ℝ) (t : ℝ) :
    heatLaplacianAverage F x t =
      ∑ i : Fin n, coordinateDerivative
        (coordinateDerivative (fun y => heatAverage F y t) i) i x := by
  rcases hF₃ with ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  let U : (Fin n → ℝ) → ℝ := fun y => heatAverage F y t
  let c : ℝ := Real.sqrt t
  have hU₂ := hasPolySecond_from_third_early
    ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩
  have hInt (i : Fin n) : Integrable
      (fun ξ : Fin n → ℝ => coordinateDerivative (coordinateDerivative F i) i
        (x + c • ξ)) (standardGaussianPi n) := by
    apply integrable_shift_poly_moment
      (contDiff_coordinateDerivative_c1_local (contDiff_coordinateDerivative_c2_local hcont i) i).continuous
      hC (fun z => htwo i i z) x c
  have hsumInt :
      ∫ ξ, ∑ i : Fin n, coordinateDerivative (coordinateDerivative F i) i
          (x + c • ξ) ∂(standardGaussianPi n) =
        ∑ i : Fin n, ∫ ξ, coordinateDerivative (coordinateDerivative F i) i
          (x + c • ξ) ∂(standardGaussianPi n) := by
    simpa using integral_finsetSum (μ := standardGaussianPi n) (s := Finset.univ)
      (f := fun i ξ => coordinateDerivative (coordinateDerivative F i) i (x + c • ξ))
      (fun i hi => hInt i)
  calc
    heatLaplacianAverage F x t =
        ∫ ξ, ∑ i : Fin n, coordinateDerivative (coordinateDerivative F i) i
          (x + c • ξ) ∂(standardGaussianPi n) := by
            simp [heatLaplacianAverage, c]
    _ = ∑ i : Fin n, heatAverage
        (coordinateDerivative (coordinateDerivative F i) i) x t := by
          rw [hsumInt]
          apply Finset.sum_congr rfl
          intro i hi
          rfl
    _ = ∑ i : Fin n, coordinateDerivative (coordinateDerivative U i) i x := by
          apply Finset.sum_congr rfl
          intro i hi
          have hfirst : coordinateDerivative U i =
              fun y => heatAverage (coordinateDerivative F i) y t := by
            funext y
            exact coordinateDerivative_heatAverage hU₂ t i y
          rw [hfirst]
          exact (coordinateDerivative_heatAverage
            (hasPolySecond_coordinateDerivative_moment
              ⟨hcont, C, hC, d, hzero, hone, htwo, hthree⟩ i) t i x).symm

private theorem hasPolyCoordinate_of_second_moment {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives F) :
    HasPolynomiallyBoundedCoordinateDerivatives F := by
  rcases hF₂.2 with ⟨C, hC, d, hzero, hone, htwo⟩
  refine ⟨hF₂.1.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2), 2 * C,
    by positivity, d, ?_, ?_⟩
  · intro x
    calc
      |F x| ≤ C * (1 + ‖x‖) ^ d := hzero x
      _ ≤ 2 * C * (1 + ‖x‖) ^ d := by
        have hn : 0 ≤ C * (1 + ‖x‖) ^ d := by positivity
        nlinarith
  · intro i x
    calc
      |F x| + |coordinateDerivative F i x| ≤
          C * (1 + ‖x‖) ^ d + C * (1 + ‖x‖) ^ d := add_le_add (hzero x) (hone i x)
      _ = 2 * C * (1 + ‖x‖) ^ d := by ring

private theorem integrable_fderiv_shift_id_moment {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F)
    (x : Fin n → ℝ) (c : ℝ) :
    Integrable (fun ξ => fderiv ℝ F (x + c • ξ) ξ) (standardGaussianPi n) := by
  rcases hF.2 with ⟨C, hC, d, hvalue, hcoordinate⟩
  let B : ℝ := (1 + ‖x‖) * (1 + |c|)
  let K : ℝ := (Fintype.card (Fin n) : ℝ) * C * B ^ d
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoly := integrable_pi_norm_power n (d + 1)
  have hmeas : Measurable (fun ξ : Fin n → ℝ => fderiv ℝ F (x + c • ξ) ξ) := by
    have hfd : Continuous (fun z : Fin n → ℝ => fderiv ℝ F z) :=
      hF.1.continuous_fderiv (by norm_num)
    exact (hfd.comp (continuous_const.add (continuous_id.const_smul c))).clm_apply
      continuous_id |>.measurable
  have hbound : ∀ ξ, |fderiv ℝ F (x + c • ξ) ξ| ≤ K * (1 + ‖ξ‖) ^ (d + 1) := by
    intro ξ
    have hcoord : ∀ i, |coordinateDerivative F i (x + c • ξ)| ≤
        C * B ^ d * (1 + ‖ξ‖) ^ d := by
      intro i
      have hbase := moment_norm_add_smul_bound x ξ c
      calc
        |coordinateDerivative F i (x + c • ξ)| ≤ C * (1 + ‖x + c • ξ‖) ^ d := by
          have h := hcoordinate i (x + c • ξ)
          exact (le_add_of_nonneg_left (abs_nonneg (F (x + c • ξ)))).trans h
        _ ≤ C * (B * (1 + ‖ξ‖)) ^ d := by gcongr
        _ = C * B ^ d * (1 + ‖ξ‖) ^ d := by dsimp [B]; rw [mul_pow]; ring
    have hfd := concentration_abs_fderiv_apply_le (x + c • ξ) ξ
      (by positivity : 0 ≤ C * B ^ d * (1 + ‖ξ‖) ^ d) hcoord
    have hξ : ‖ξ‖ ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
    calc
      |fderiv ℝ F (x + c • ξ) ξ| ≤
          (Fintype.card (Fin n) : ℝ) * ‖ξ‖ *
            (C * B ^ d * (1 + ‖ξ‖) ^ d) := hfd
      _ ≤ K * (1 + ‖ξ‖) ^ (d + 1) := by
        dsimp [K]
        calc
          (Fintype.card (Fin n) : ℝ) * ‖ξ‖ *
              (C * B ^ d * (1 + ‖ξ‖) ^ d) =
              ((Fintype.card (Fin n) : ℝ) * C * B ^ d) *
                (‖ξ‖ * (1 + ‖ξ‖) ^ d) := by ring
          _ ≤ ((Fintype.card (Fin n) : ℝ) * C * B ^ d) *
                ((1 + ‖ξ‖) * (1 + ‖ξ‖) ^ d) := by
              apply mul_le_mul_of_nonneg_left
              · exact mul_le_mul_of_nonneg_right hξ (by positivity)
              · positivity
          _ = ((Fintype.card (Fin n) : ℝ) * C * B ^ d) *
                (1 + ‖ξ‖) ^ (d + 1) := by rw [pow_succ]; ring
  apply integrable_of_pi_polynomial_bound hmeas hK (d := d + 1)
  intro ξ
  simpa [Real.norm_eq_abs] using hbound ξ

private theorem trace_second_exp_linear_local {n : ℕ}
    {U : (Fin n → ℝ) → ℝ} (hU₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives U)
    (lam : ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, coordinateDerivative
      (coordinateDerivative (fun y => Real.exp (lam * U y)) i) i x) =
      lam ^ 2 * Real.exp (lam * U x) *
        (∑ i : Fin n, (coordinateDerivative U i x) ^ 2) +
      lam * Real.exp (lam * U x) *
        (∑ i : Fin n, coordinateDerivative (coordinateDerivative U i) i x) := by
  calc
    _ = ∑ i : Fin n,
        (lam ^ 2 * Real.exp (lam * U x) * coordinateDerivative U i x *
            coordinateDerivative U i x +
          lam * Real.exp (lam * U x) *
            coordinateDerivative (coordinateDerivative U i) i x) := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa using coordinateDerivative_second_exp_linear_local hU₂.1 lam i i x
    _ = _ := by
      calc
        (∑ i : Fin n,
            (lam ^ 2 * Real.exp (lam * U x) * coordinateDerivative U i x *
                coordinateDerivative U i x +
              lam * Real.exp (lam * U x) *
                coordinateDerivative (coordinateDerivative U i) i x)) =
            (∑ i : Fin n,
              (lam ^ 2 * Real.exp (lam * U x)) *
                  (coordinateDerivative U i x) ^ 2) +
              ∑ i : Fin n,
                (lam * Real.exp (lam * U x)) *
                  coordinateDerivative (coordinateDerivative U i) i x := by
          rw [Finset.sum_add_distrib]
          congr 1
          · apply Finset.sum_congr rfl
            intro i hi
            ring
        _ = lam ^ 2 * Real.exp (lam * U x) *
              (∑ i : Fin n, (coordinateDerivative U i x) ^ 2) +
              lam * Real.exp (lam * U x) *
                (∑ i : Fin n,
                  coordinateDerivative (coordinateDerivative U i) i x) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]

private theorem hasDerivAt_gaussian_heatMoment_integral_derivative {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {B L lam : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hFbound : ∀ x, |F x| ≤ B)
    (hgrad : ∀ i x, |coordinateDerivative F i x| ≤ L)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun r => ∫ ξ, gaussianHeatMomentIntegrand F lam r ξ
        ∂(standardGaussianPi n))
      (∫ ξ, gaussianHeatMomentIntegrandDerivative F lam t ξ
        ∂(standardGaussianPi n)) t := by
  obtain ⟨Clap, hClap, d, hLapBound⟩ := abs_heatLaplacianAverage_le_of_third_local hF₃
  let δ : ℝ := min (t / 2) ((1 - t) / 2)
  let Q : ℝ := Real.exp (|lam| * B)
  let A : ℝ := (Fintype.card (Fin n) : ℝ) * L /
    (2 * Real.sqrt (t / 2))
  let K : ℝ := |lam| * Q * (A + Clap / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hK : 0 ≤ K := by dsimp [K, A]; positivity
  have hpoly := integrable_pi_norm_power n (d + 1)
  have hbound : ∀ᵐ ξ ∂(standardGaussianPi n), ∀ r ∈ Metric.ball t δ,
      ‖gaussianHeatMomentIntegrandDerivative F lam r ξ‖ ≤
        K * (1 + ‖ξ‖) ^ (d + 1) := by
    apply ae_of_all
    intro ξ r hr
    have hdist : |r - t| < δ := by simpa [Real.dist_eq] using Metric.mem_ball.mp hr
    have hlow : t / 2 < r := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hsmall : δ ≤ t / 2 := min_le_left _ _
      linarith
    have hupp : r < (1 + t) / 2 := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hsmall : δ ≤ (1 - t) / 2 := min_le_right _ _
      linarith
    have hr0 : 0 < r := by linarith
    have hr1' : r < 1 := by linarith
    have hsqrt : Real.sqrt r ≤ 1 := by rw [Real.sqrt_le_one]; linarith
    have hcenter : ‖Real.sqrt r • ξ‖ ≤ ‖ξ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg ξ) hsqrt
    have hheatGrad (i : Fin n) :
        |coordinateDerivative (fun x => heatAverage F x (1 - r)) i
            (Real.sqrt r • ξ)| ≤ L := by
      exact abs_coordinateDerivative_heatAverage_le_local hF₃ hL hgrad i
        (Real.sqrt r • ξ) (1 - r)
    have hspatial : |fderiv ℝ (fun x => heatAverage F x (1 - r))
        (Real.sqrt r • ξ) ξ| ≤
        (Fintype.card (Fin n) : ℝ) * ‖ξ‖ * L :=
      concentration_abs_fderiv_apply_le _ _ hL hheatGrad
    have hden : 2 * Real.sqrt (t / 2) ≤ 2 * Real.sqrt r := by
      gcongr
    have hrecip : (2 * Real.sqrt r)⁻¹ ≤ (2 * Real.sqrt (t / 2))⁻¹ :=
      by simpa [one_div] using one_div_le_one_div_of_le (by positivity) hden
    have hspatialTerm :
        |fderiv ℝ (fun x => heatAverage F x (1 - r))
          (Real.sqrt r • ξ) ξ / (2 * Real.sqrt r)| ≤ A * ‖ξ‖ := by
      rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.sqrt r)]
      dsimp [A]
      rw [div_eq_mul_inv]
      calc
        |fderiv ℝ (fun x => heatAverage F x (1 - r))
            (Real.sqrt r • ξ) ξ| * (2 * Real.sqrt r)⁻¹ ≤
            ((Fintype.card (Fin n) : ℝ) * ‖ξ‖ * L) *
              (2 * Real.sqrt r)⁻¹ := by
                gcongr
        _ ≤ ((Fintype.card (Fin n) : ℝ) * ‖ξ‖ * L) *
              (2 * Real.sqrt (t / 2))⁻¹ := by
                have hnonneg : 0 ≤ (Fintype.card (Fin n) : ℝ) * ‖ξ‖ * L := by positivity
                exact mul_le_mul_of_nonneg_left hrecip hnonneg
        _ = ((Fintype.card (Fin n) : ℝ) * L *
              (2 * Real.sqrt (t / 2))⁻¹) * ‖ξ‖ := by ring
        _ = A * ‖ξ‖ := by dsimp [A]; rw [div_eq_mul_inv]; ring
    have hLap : |heatLaplacianAverage F (Real.sqrt r • ξ) (1 - r)| ≤
        Clap * (1 + ‖ξ‖) ^ d := by
      apply (hLapBound (Real.sqrt r • ξ) (1 - r) (by linarith) (by linarith)).trans
      gcongr
    have hbridge : |gaussianHeatMomentBridgeDerivative F r ξ| ≤
        (A + Clap / 2) * (1 + ‖ξ‖) ^ (d + 1) := by
      rw [gaussianHeatMomentBridgeDerivative]
      have hpow : 1 + ‖ξ‖ ≤ (1 + ‖ξ‖) ^ (d + 1) := by
        have hbase : 1 ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
        calc
          1 + ‖ξ‖ = (1 + ‖ξ‖) * 1 := by ring
          _ ≤ (1 + ‖ξ‖) * (1 + ‖ξ‖) ^ d :=
            mul_le_mul_of_nonneg_left (one_le_pow₀ hbase) (by positivity)
          _ = (1 + ‖ξ‖) ^ (d + 1) := by rw [pow_succ]; ring
      have hpowd : (1 + ‖ξ‖) ^ d ≤ (1 + ‖ξ‖) ^ (d + 1) := by
        exact (pow_le_pow_right₀ (by linarith [norm_nonneg ξ] : 1 ≤ 1 + ‖ξ‖)
          (Nat.le_succ d))
      calc
        |fderiv ℝ (fun x => heatAverage F x (1 - r))
              (Real.sqrt r • ξ) ξ / (2 * Real.sqrt r) -
            (1 / 2 : ℝ) * heatLaplacianAverage F (Real.sqrt r • ξ) (1 - r)| ≤
            |fderiv ℝ (fun x => heatAverage F x (1 - r))
              (Real.sqrt r • ξ) ξ / (2 * Real.sqrt r)| +
              |(1 / 2 : ℝ) * heatLaplacianAverage F (Real.sqrt r • ξ) (1 - r)| :=
          abs_sub _ _
        _ ≤ A * ‖ξ‖ + (Clap / 2) * (1 + ‖ξ‖) ^ d :=
          add_le_add hspatialTerm (by
            rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
            calc
              (1 / 2 : ℝ) * |heatLaplacianAverage F (Real.sqrt r • ξ) (1 - r)| ≤
                  (1 / 2 : ℝ) * (Clap * (1 + ‖ξ‖) ^ d) := by gcongr
              _ = (Clap / 2) * (1 + ‖ξ‖) ^ d := by ring)
        _ ≤ A * (1 + ‖ξ‖) ^ (d + 1) +
              (Clap / 2) * (1 + ‖ξ‖) ^ (d + 1) := by
          have hnorm : ‖ξ‖ ≤ 1 + ‖ξ‖ := by linarith [norm_nonneg ξ]
          exact add_le_add (mul_le_mul_of_nonneg_left (hnorm.trans hpow) hA)
            (mul_le_mul_of_nonneg_left hpowd (by positivity))
        _ = (A + Clap / 2) * (1 + ‖ξ‖) ^ (d + 1) := by ring
    have hmoment : |gaussianHeatMomentIntegrand F lam r ξ| ≤ Q := by
      simpa [Q] using abs_gaussianHeatMomentIntegrand_le_of_bounded hF₃ hB hFbound lam r ξ
    rw [gaussianHeatMomentIntegrandDerivative, Real.norm_eq_abs]
    rw [abs_mul, abs_mul]
    calc
      |lam| * |gaussianHeatMomentIntegrand F lam r ξ| *
          |gaussianHeatMomentBridgeDerivative F r ξ| ≤
          |lam| * Q * ((A + Clap / 2) * (1 + ‖ξ‖) ^ (d + 1)) := by
        gcongr
      _ = K * (1 + ‖ξ‖) ^ (d + 1) := by dsimp [K]; ring
  have hboundInt : Integrable (fun ξ : Fin n → ℝ =>
      K * (1 + ‖ξ‖) ^ (d + 1)) (standardGaussianPi n) := by
    simpa using hpoly.const_mul K
  have hmeas : ∀ᶠ r in 𝓝 t,
      AEStronglyMeasurable (gaussianHeatMomentIntegrand F lam r)
        (standardGaussianPi n) := by
    filter_upwards with r
    have hU := contDiff_two_heatAverage_of_third hF₃ (1 - r)
    have harg : Continuous (fun ξ : Fin n → ℝ =>
        lam * heatAverage F (Real.sqrt r • ξ) (1 - r)) := by
      have hcenter : Continuous (fun ξ : Fin n → ℝ => (Real.sqrt r : ℝ) • ξ) := by fun_prop
      exact continuous_const.mul (hU.continuous.comp hcenter)
    have hcontinuous : Continuous (fun ξ : Fin n → ℝ =>
        gaussianHeatMomentIntegrand F lam r ξ) := by
      change Continuous (fun ξ => Real.exp (lam * heatAverage F (Real.sqrt r • ξ) (1 - r)))
      exact Real.continuous_exp.comp harg
    exact hcontinuous.measurable.aestronglyMeasurable
  have hmomentInt : Integrable (gaussianHeatMomentIntegrand F lam t)
      (standardGaussianPi n) := by
    have hmajor : Integrable (fun _ : Fin n → ℝ => Q) (standardGaussianPi n) := integrable_const Q
    refine Integrable.mono' hmajor
      (by
        have hU := contDiff_two_heatAverage_of_third hF₃ (1 - t)
        have harg : Continuous (fun ξ : Fin n → ℝ =>
            lam * heatAverage F (Real.sqrt t • ξ) (1 - t)) :=
          continuous_const.mul (hU.continuous.comp (by fun_prop))
        have hcontinuous : Continuous (fun ξ : Fin n → ℝ =>
            gaussianHeatMomentIntegrand F lam t ξ) := by
          change Continuous (fun ξ => Real.exp (lam * heatAverage F (Real.sqrt t • ξ) (1 - t)))
          exact Real.continuous_exp.comp harg
        exact hcontinuous.measurable.aestronglyMeasurable) ?_
    filter_upwards with ξ
    have hpoint := abs_gaussianHeatMomentIntegrand_le_of_bounded hF₃ hB hFbound lam t ξ
    simpa [Real.norm_eq_abs] using hpoint
  have hFprimeMeas : AEStronglyMeasurable
      (gaussianHeatMomentIntegrandDerivative F lam t) (standardGaussianPi n) := by
    have hU := contDiff_two_heatAverage_of_third hF₃ (1 - t)
    have hfdcont : Continuous (fun x : Fin n → ℝ =>
        fderiv ℝ (fun y => heatAverage F y (1 - t)) x) :=
      hU.continuous_fderiv (by norm_num)
    have hpathcont : Continuous (fun ξ : Fin n → ℝ =>
        gaussianHeatMomentBridgeDerivative F t ξ) := by
      have hLaplacian := continuous_heatLaplacianAverage_of_third hF₃ (1 - t)
      have hcenter : Continuous (fun ξ : Fin n → ℝ => Real.sqrt t • ξ) :=
        by fun_prop
      have hfirst : Continuous (fun ξ : Fin n → ℝ =>
          fderiv ℝ (fun y => heatAverage F y (1 - t)) (Real.sqrt t • ξ) ξ) :=
        (hfdcont.comp hcenter).clm_apply continuous_id
      have hsecond : Continuous (fun ξ : Fin n → ℝ =>
          (1 / 2 : ℝ) * heatLaplacianAverage F (Real.sqrt t • ξ) (1 - t)) :=
        continuous_const.mul (hLaplacian.comp hcenter)
      dsimp [gaussianHeatMomentBridgeDerivative]
      exact hfirst.div_const (2 * Real.sqrt t) |>.sub hsecond
    have hmomentCont : Continuous (gaussianHeatMomentIntegrand F lam t) := by
      have harg : Continuous (fun ξ : Fin n → ℝ =>
          lam * heatAverage F (Real.sqrt t • ξ) (1 - t)) :=
        continuous_const.mul (hU.continuous.comp (by fun_prop))
      change Continuous (fun ξ => Real.exp (lam * heatAverage F (Real.sqrt t • ξ) (1 - t)))
      exact Real.continuous_exp.comp harg
    have hderivCont : Continuous (gaussianHeatMomentIntegrandDerivative F lam t) := by
      change Continuous (fun ξ => lam * gaussianHeatMomentIntegrand F lam t ξ *
        gaussianHeatMomentBridgeDerivative F t ξ)
      exact (hmomentCont.const_mul lam).mul hpathcont
    exact hderivCont.measurable.aestronglyMeasurable
  have hdiff : ∀ᵐ ξ ∂(standardGaussianPi n), ∀ r ∈ Metric.ball t δ,
      HasDerivAt (fun s => gaussianHeatMomentIntegrand F lam s ξ)
        (gaussianHeatMomentIntegrandDerivative F lam r ξ) r := by
    apply ae_of_all
    intro ξ r hr
    have hdist : |r - t| < δ := by simpa [Real.dist_eq] using Metric.mem_ball.mp hr
    have hlow : t / 2 < r := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hsmall : δ ≤ t / 2 := min_le_left _ _
      linarith
    have hupp : r < (1 + t) / 2 := by
      dsimp [δ] at hdist
      rw [abs_lt] at hdist
      have hsmall : δ ≤ (1 - t) / 2 := min_le_right _ _
      linarith
    exact hasDerivAt_gaussian_heatMoment_integrand hF₃ lam ξ (by linarith) (by linarith)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun r ξ => gaussianHeatMomentIntegrand F lam r ξ) (x₀ := t)
    (s := Metric.ball t δ)
    (F' := fun r ξ => gaussianHeatMomentIntegrandDerivative F lam r ξ)
    (bound := fun ξ => K * (1 + ‖ξ‖) ^ (d + 1))
    (Metric.ball_mem_nhds t hδ) hmeas hmomentInt hFprimeMeas hbound hboundInt hdiff
  exact hderiv.2

/-- The Gaussian heat average of the Laplacian of a `C³` function has polynomial growth,
uniformly for heat times in `[0,1]`. -/
theorem abs_heatLaplacianAverage_le_of_third {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ (x : Fin n → ℝ) (t : ℝ),
      0 ≤ t → t ≤ 1 →
        |heatLaplacianAverage F x t| ≤ C * (1 + ‖x‖) ^ d := by
  rcases hF₃ with ⟨hFcont, C, hC, d, hzero, hone, htwo, hthree⟩
  let H : (Fin n → ℝ) → ℝ := fun x =>
    ∑ i : Fin n, coordinateDerivative (coordinateDerivative F i) i x
  let C₀ : ℝ := (Fintype.card (Fin n) : ℝ) * C
  let M : ℝ := ∫ ξ, (1 + ‖ξ‖) ^ d ∂(standardGaussianPi n)
  let C₁ : ℝ := C₀ * 2 ^ d * M
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hM : 0 ≤ M := by
    apply integral_nonneg
    intro ξ
    positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hHcont : Continuous H := by
    apply continuous_finsetSum
    intro i hi
    have hcoord : ContDiff ℝ 1 (coordinateDerivative (coordinateDerivative F i) i) :=
      contDiff_coordinateDerivative_c1_local
        (contDiff_coordinateDerivative_c2_local hFcont i) i
    exact hcoord.continuous
  have hHbound : ∀ x, |H x| ≤ C₀ * (1 + ‖x‖) ^ d := by
    intro x
    calc
      |H x| ≤ ∑ i : Fin n,
          |coordinateDerivative (coordinateDerivative F i) i x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, C * (1 + ‖x‖) ^ d := by
        apply Finset.sum_le_sum
        intro i hi
        exact htwo i i x
      _ = C₀ * (1 + ‖x‖) ^ d := by
        simp [C₀, Finset.sum_const, nsmul_eq_mul]
        ring
  refine ⟨C₁, hC₁, d, ?_⟩
  intro x t ht0 ht1
  let c : ℝ := Real.sqrt t
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hc1 : c ≤ 1 := by
    dsimp [c]
    rw [Real.sqrt_le_one]
    exact ht1
  have hca : |c| ≤ 1 := by simpa [abs_of_nonneg hc0] using hc1
  have hshift := abs_shiftAverage_le_of_polynomial_bound hHcont hC₀ hHbound x c
  have hfactor : (1 + |c|) ^ d ≤ 2 ^ d := by
    gcongr
    linarith
  have hfactor_nonneg : 0 ≤ C₀ * (1 + |c|) ^ d * M := by positivity
  have hbound := calc
    |shiftAverage H x c| ≤ (C₀ * (1 + |c|) ^ d * M) * (1 + ‖x‖) ^ d := hshift
    _ ≤ (C₀ * 2 ^ d * M) * (1 + ‖x‖) ^ d := by
      gcongr
  simpa [heatLaplacianAverage, H, shiftAverage, c, M, C₀, C₁] using hbound

private theorem integral_gaussianHeatMomentIntegrandDerivative_eq {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {B L lam : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hFbound : ∀ x, |F x| ≤ B)
    (hgrad : ∀ x, ‖coordinateGradientEuclidean F x‖ ≤ L)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    ∫ ξ, gaussianHeatMomentIntegrandDerivative F lam t ξ
      ∂(standardGaussianPi n) =
      (lam ^ 2 / 2) * ∫ ξ,
        Real.exp (lam * heatAverage F (Real.sqrt t • ξ) (1 - t)) *
          ∑ i : Fin n,
            (coordinateDerivative (fun x => heatAverage F x (1 - t)) i
              (Real.sqrt t • ξ)) ^ 2 ∂(standardGaussianPi n) := by
  let U : (Fin n → ℝ) → ℝ := fun x => heatAverage F x (1 - t)
  let E : (Fin n → ℝ) → ℝ := fun x => Real.exp (lam * U x)
  let P : (Fin n → ℝ) → ℝ := fun x => E x * heatLaplacianAverage F x (1 - t)
  let R : (Fin n → ℝ) → ℝ := fun x => E x *
    ∑ i : Fin n, (coordinateDerivative U i x) ^ 2
  have hU₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives U := by
    exact hasPolynomiallyBoundedSecond_heatAverage_of_third hF₃ (1 - t)
  have hUbound : ∀ x, |U x| ≤ B := by
    intro x
    exact abs_heatAverage_le_of_bounded_local hF₃ hB hFbound x (1 - t)
  have hgradU : ∀ i x, |coordinateDerivative U i x| ≤ L := by
    intro i x
    have hnorm := norm_coordinateGradient_heatAverage_le hF₃ hgrad x (1 - t)
    have hcoord := abs_coordinate_le_euclidean_norm_local
      (coordinateGradientEuclidean U x) i
    simpa [U, coordinateGradientEuclidean] using hcoord.trans hnorm
  have hG₂ : HasPolynomiallyBoundedSecondCoordinateDerivatives E :=
    hasPolynomiallyBoundedSecond_exp_linear_local hU₂ hL hUbound hgradU
  have hG₁ : HasPolynomiallyBoundedCoordinateDerivatives E :=
    hasPolyCoordinate_of_second_moment hG₂
  have hU₁ : ContDiff ℝ 1 U := hU₂.1.of_le (by norm_num)
  have hexp (x : Fin n → ℝ) : |E x| ≤ Real.exp (|lam| * B) := by
    change |Real.exp (lam * U x)| ≤ _
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      lam * U x ≤ |lam * U x| := le_abs_self _
      _ = |lam| * |U x| := abs_mul _ _
      _ ≤ |lam| * B := mul_le_mul_of_nonneg_left (hUbound x) (abs_nonneg _)
  obtain ⟨Clap, hClap, d, hLap⟩ := abs_heatLaplacianAverage_le_of_third hF₃
  have hPcont : Continuous P := by
    dsimp [P, E, U]
    exact (Real.continuous_exp.comp
      (continuous_const.mul ((hU₂.1.continuous).comp continuous_id))).mul
        (continuous_heatLaplacianAverage_of_third hF₃ (1 - t))
  have hPbound (x : Fin n → ℝ) :
      |P x| ≤ (Real.exp (|lam| * B) * Clap) * (1 + ‖x‖) ^ d := by
    dsimp [P]
    rw [abs_mul]
    calc
      |E x| * |heatLaplacianAverage F x (1 - t)| ≤
          Real.exp (|lam| * B) * (Clap * (1 + ‖x‖) ^ d) := by
            gcongr
            · exact hexp x
            · exact hLap x (1 - t) (by linarith) (by linarith)
      _ = (Real.exp (|lam| * B) * Clap) * (1 + ‖x‖) ^ d := by ring
  have hPInt : Integrable (fun ξ : Fin n → ℝ => P (Real.sqrt t • ξ))
      (standardGaussianPi n) := by
    have h := integrable_shift_poly_moment hPcont (by positivity) (d := d)
      (fun x => hPbound x) (0 : Fin n → ℝ) (Real.sqrt t)
    simpa only [zero_add] using h
  have hsumUcont : Continuous (fun x : Fin n → ℝ =>
      ∑ i : Fin n, (coordinateDerivative U i x) ^ 2) := by
    apply continuous_finsetSum
    intro i hi
    exact (contDiff_coordinateDerivative_c1_local hU₂.1 i).continuous.pow 2
  have hRcont : Continuous R := (Real.continuous_exp.comp
      (continuous_const.mul (hU₂.1.continuous))).mul hsumUcont
  have hRbound (x : Fin n → ℝ) : |R x| ≤
      (Real.exp (|lam| * B) * (Fintype.card (Fin n) : ℝ) * L ^ 2) := by
    dsimp [R]
    have hsumNonneg : 0 ≤ ∑ i : Fin n, (coordinateDerivative U i x) ^ 2 :=
      Finset.sum_nonneg fun i hi => sq_nonneg _
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hsumNonneg]
    have hsum : (∑ i : Fin n, (coordinateDerivative U i x) ^ 2) ≤
        (Fintype.card (Fin n) : ℝ) * L ^ 2 := by
      calc
        (∑ i : Fin n, (coordinateDerivative U i x) ^ 2) ≤
            ∑ _i : Fin n, L ^ 2 := by
              apply Finset.sum_le_sum
              intro i hi
              have h := hgradU i x
              have habs := abs_le.mp h
              nlinarith [sq_nonneg (coordinateDerivative U i x),
                sq_nonneg (coordinateDerivative U i x - L),
                sq_nonneg (coordinateDerivative U i x + L)]
        _ = (Fintype.card (Fin n) : ℝ) * L ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]
    change Real.exp (lam * U x) *
        (∑ i : Fin n, (coordinateDerivative U i x) ^ 2) ≤ _
    have hEupper : Real.exp (lam * U x) ≤ Real.exp (|lam| * B) := by
      simpa [E, abs_of_pos (Real.exp_pos _)] using hexp x
    calc
      Real.exp (lam * U x) * (∑ i : Fin n, (coordinateDerivative U i x) ^ 2) ≤
          Real.exp (|lam| * B) * ((Fintype.card (Fin n) : ℝ) * L ^ 2) := by
            exact mul_le_mul hEupper hsum hsumNonneg (le_of_lt (Real.exp_pos _))
      _ = Real.exp (|lam| * B) * (Fintype.card (Fin n) : ℝ) * L ^ 2 := by ring
  have hRInt : Integrable (fun ξ : Fin n → ℝ => R (Real.sqrt t • ξ))
      (standardGaussianPi n) := by
    let C₀ : ℝ := Real.exp (|lam| * B) * (Fintype.card (Fin n) : ℝ) * L ^ 2
    have h := integrable_shift_poly_moment hRcont (C := C₀) (by positivity) (d := 0)
      (fun x => by simpa [C₀] using hRbound x) (0 : Fin n → ℝ) (Real.sqrt t)
    simpa only [zero_add] using h
  have hfdGInt : Integrable
      (fun ξ : Fin n → ℝ => fderiv ℝ E (Real.sqrt t • ξ) ξ)
      (standardGaussianPi n) := by
    simpa [E, zero_add] using integrable_fderiv_shift_id_moment hG₁
      (0 : Fin n → ℝ) (Real.sqrt t)
  have hfdG (x v : Fin n → ℝ) :
      fderiv ℝ E x v = lam * E x * fderiv ℝ U x v := by
    rw [concentration_fderiv_apply_eq_sum, concentration_fderiv_apply_eq_sum]
    calc
      (∑ i : Fin n, v i * coordinateDerivative E i x) =
          ∑ i : Fin n, v i * (lam * E x * coordinateDerivative U i x) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [coordinateDerivative_exp_linear_local hU₁ (lam := lam) i x]
      _ = lam * E x * (∑ i : Fin n, v i * coordinateDerivative U i x) := by
            calc
              (∑ i : Fin n, v i * (lam * E x * coordinateDerivative U i x)) =
                  ∑ i : Fin n, (lam * E x) *
                    (v i * coordinateDerivative U i x) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      ring
              _ = lam * E x * (∑ i : Fin n, v i * coordinateDerivative U i x) := by
                    exact (Finset.mul_sum Finset.univ
                      (fun i : Fin n => v i * coordinateDerivative U i x)
                      (lam * E x)).symm
  have htrace (x : Fin n → ℝ) :
      (∑ i : Fin n, coordinateDerivative (coordinateDerivative E i) i x) =
        lam ^ 2 * E x * (∑ i : Fin n, (coordinateDerivative U i x) ^ 2) +
          lam * P x := by
    rw [trace_second_exp_linear_local hU₂ lam x]
    have hheat := heatLaplacianAverage_eq_trace_heatAverage hF₃ x (1 - t)
    have hheat' : heatLaplacianAverage F x (1 - t) =
        ∑ i : Fin n, coordinateDerivative (coordinateDerivative U i) i x := by
      simpa [U] using hheat
    simp only [P, E]
    rw [← hheat']
    ring
  have hscaled := integral_fderiv_shift_scaled_eq_sqrt_mul_laplacian
    hG₁ hG₂ (0 : Fin n → ℝ) ht
  have hscaled' :
      ∫ ξ, fderiv ℝ E (Real.sqrt t • ξ) ξ ∂(standardGaussianPi n) =
        Real.sqrt t * ∫ ξ,
          ∑ i : Fin n, coordinateDerivative (coordinateDerivative E i) i
            (Real.sqrt t • ξ) ∂(standardGaussianPi n) := by
    simpa [zero_add] using hscaled
  have htraceInt :
      ∫ ξ, ∑ i : Fin n, coordinateDerivative (coordinateDerivative E i) i
          (Real.sqrt t • ξ) ∂(standardGaussianPi n) =
        lam ^ 2 * ∫ ξ, R (Real.sqrt t • ξ) ∂(standardGaussianPi n) +
          lam * ∫ ξ, P (Real.sqrt t • ξ) ∂(standardGaussianPi n) := by
    calc
      _ = ∫ ξ, (lam ^ 2 * R (Real.sqrt t • ξ) + lam * P (Real.sqrt t • ξ))
            ∂(standardGaussianPi n) := by
          apply integral_congr_ae
          exact ae_of_all _ fun ξ => by
            simpa [R, E, mul_assoc] using htrace (Real.sqrt t • ξ)
      _ = _ := by
        rw [integral_add (hRInt.const_mul _) (hPInt.const_mul _),
          integral_const_mul, integral_const_mul]
  have hpoint (ξ : Fin n → ℝ) :
      gaussianHeatMomentIntegrandDerivative F lam t ξ =
        (1 / (2 * Real.sqrt t)) * fderiv ℝ E (Real.sqrt t • ξ) ξ -
          (lam / 2) * P (Real.sqrt t • ξ) := by
    rw [gaussianHeatMomentIntegrandDerivative, gaussianHeatMomentBridgeDerivative,
      gaussianHeatMomentIntegrand]
    rw [hfdG]
    dsimp [P, E, U]
    ring
  calc
    ∫ ξ, gaussianHeatMomentIntegrandDerivative F lam t ξ ∂(standardGaussianPi n) =
        (1 / (2 * Real.sqrt t)) *
            ∫ ξ, fderiv ℝ E (Real.sqrt t • ξ) ξ ∂(standardGaussianPi n) -
          (lam / 2) * ∫ ξ, P (Real.sqrt t • ξ) ∂(standardGaussianPi n) := by
      rw [integral_congr_ae (ae_of_all _ hpoint),
        integral_sub (hfdGInt.const_mul _) (hPInt.const_mul _),
        integral_const_mul, integral_const_mul]
    _ = (lam ^ 2 / 2) * ∫ ξ, R (Real.sqrt t • ξ) ∂(standardGaussianPi n) := by
      rw [hscaled', htraceInt]
      have hsqrt : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
      field_simp [hsqrt]
      ring
    _ = _ := by
      simp [R, E, U]

/-- The exponential moment along the Gaussian heat interpolation. -/
noncomputable def gaussianHeatMoment {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (lam t : ℝ) : ℝ :=
  ∫ ξ, Real.exp (lam * heatAverage F (Real.sqrt t • ξ) (1 - t))
    ∂(standardGaussianPi n)

/-- The Gaussian heat interpolation moment has the exact derivative obtained by cancellation of
the backward heat term against Gaussian integration by parts. -/
theorem hasDerivAt_gaussianHeatMoment {n : ℕ}
    {F : (Fin n → ℝ) → ℝ}
    (hF₃ : HasPolynomiallyBoundedThirdCoordinateDerivatives F)
    {B L lam : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hFbound : ∀ x, |F x| ≤ B)
    (hgrad : ∀ x, ‖coordinateGradientEuclidean F x‖ ≤ L)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun r => gaussianHeatMoment F lam r)
      ((lam ^ 2 / 2) * ∫ ξ,
        Real.exp (lam * heatAverage F (Real.sqrt t • ξ) (1 - t)) *
          ∑ i : Fin n,
            (coordinateDerivative (fun x => heatAverage F x (1 - t)) i
              (Real.sqrt t • ξ)) ^ 2 ∂(standardGaussianPi n)) t := by
  have hcoord : ∀ i x, |coordinateDerivative F i x| ≤ L := by
    intro i x
    exact (abs_coordinate_le_euclidean_norm_local
      (coordinateGradientEuclidean F x) i).trans (hgrad x)
  have hbase := hasDerivAt_gaussian_heatMoment_integral_derivative
    hF₃ (lam := lam) hB hL hFbound hcoord ht ht1
  have hcancel := integral_gaussianHeatMomentIntegrandDerivative_eq
    hF₃ (lam := lam) hB hL hFbound hgrad ht ht1
  change HasDerivAt
    (fun r => ∫ ξ, gaussianHeatMomentIntegrand F lam r ξ ∂(standardGaussianPi n)) _ t
  exact hbase.congr_deriv hcancel

end ASDExplicitGamma.Gaussian
