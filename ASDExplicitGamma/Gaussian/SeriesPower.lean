/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.SeriesPassage
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Real-power observables for Gaussian heat flow
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace ASDExplicitGamma.Gaussian

private lemma fderiv_rpow_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : E → ℝ} (hΦ : ContDiff ℝ 2 Φ) {p : ℝ} (hp : 2 ≤ p) (y : E) :
    fderiv ℝ (fun z => Φ z ^ p) y = (p * Φ y ^ (p - 1)) • fderiv ℝ Φ y := by
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hΦ' := (hΦ1.differentiable_one y).hasFDerivAt
  have hpow := hΦ'.rpow_const (Or.inr (by linarith))
  exact hpow.fderiv

private lemma fderiv_fderiv_rpow_comp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) {p : ℝ} (hp : 2 ≤ p) (y u w : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun q => Φ q ^ p) z w) y u =
      p * Φ y ^ (p - 1) * fderiv ℝ (fun z => fderiv ℝ Φ z w) y u +
        p * (p - 1) * Φ y ^ (p - 2) * (fderiv ℝ Φ y u) * (fderiv ℝ Φ y w) := by
  let A : E → ℝ := fun z => p * Φ z ^ (p - 1)
  let B : E → ℝ := fun z => fderiv ℝ Φ z w
  have hinner (z : E) : fderiv ℝ (fun q => Φ q ^ p) z w = A z * B z := by
    rw [fderiv_rpow_comp hΦ hp z]
    simp [A, B, smul_apply, smul_eq_mul, mul_assoc]
  have hAB : (fun z => fderiv ℝ (fun q => Φ q ^ p) z w) = fun z => A z * B z :=
    funext hinner
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hΦder : HasFDerivAt Φ (fderiv ℝ Φ y) y := (hΦ1.differentiable_one y).hasFDerivAt
  have hAder : HasFDerivAt A
      ((p * (p - 1) * Φ y ^ (p - 2)) • fderiv ℝ Φ y) y := by
    have hpow := hΦder.rpow_const (Or.inr (by linarith : 1 ≤ p - 1))
    have hexp : p - 1 - 1 = p - 2 := by ring
    simpa [A, hexp, smul_smul, mul_assoc, mul_left_comm, mul_comm] using hpow.const_mul p
  have hBcont : ContDiff ℝ 1 B := by
    have h := hΦ.contDiff_fderiv_apply (m := 1)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hpair : ContDiff ℝ 1 (fun z : E => (z, w)) := contDiff_id.prodMk contDiff_const
    simpa [B, Function.comp_def] using h.comp hpair
  have hBder : HasFDerivAt B (fderiv ℝ B y) y := (hBcont.differentiable_one y).hasFDerivAt
  have hprod := (hAder.mul hBder).fderiv
  rw [hAB]
  have hEval := congrArg (fun L : E →L[ℝ] ℝ => L u) hprod
  have hEval' : (fderiv ℝ (fun z => A z * B z) y) u =
      A y * fderiv ℝ B y u +
        (p * (p - 1) * Φ y ^ (p - 2) * fderiv ℝ Φ y u) * B y := by
    calc
      _ = (fderiv ℝ (A * B) y) u := rfl
      _ = (A y • fderiv ℝ B y +
          B y • (p * (p - 1) * Φ y ^ (p - 2)) • fderiv ℝ Φ y) u := hEval
      _ = _ := by
        simp [smul_apply,
          smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  calc
    _ = A y * fderiv ℝ B y u +
          (p * (p - 1) * Φ y ^ (p - 2) * fderiv ℝ Φ y u) * B y := hEval'
    _ = p * Φ y ^ (p - 1) * fderiv ℝ (fun z => fderiv ℝ Φ z w) y u +
          p * (p - 1) * Φ y ^ (p - 2) * (fderiv ℝ Φ y u) * (fderiv ℝ Φ y w) := by
      simp only [A, B]

private lemma secondDirectionalDerivative_rpow_comp {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) {p : ℝ} (hp : 2 ≤ p) (y w : E) :
    secondDirectionalDerivative (fun z => Φ z ^ p) y w =
      p * Φ y ^ (p - 1) * secondDirectionalDerivative Φ y w +
        p * (p - 1) * Φ y ^ (p - 2) * (fderiv ℝ Φ y w) ^ 2 := by
  change fderiv ℝ (fun z => fderiv ℝ (fun q => Φ q ^ p) z w) y w = _
  calc
    _ = p * Φ y ^ (p - 1) * fderiv ℝ (fun z => fderiv ℝ Φ z w) y w +
          p * (p - 1) * Φ y ^ (p - 2) * (fderiv ℝ Φ y w) * (fderiv ℝ Φ y w) :=
        fderiv_fderiv_rpow_comp hΦ hp y w w
    _ = _ := by
      simp only [secondDirectionalDerivative, pow_two]
      ring

private lemma rpow_le_polynomial_envelope {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦnonneg : ∀ y, 0 ≤ Φ y) {C : ℝ} (hC : 0 ≤ C) (d : ℕ)
    (hvalue : ∀ y, |Φ y| ≤ C * (1 + ‖y‖) ^ d) {p : ℝ}
    (y : E) (r : ℝ) (hr : 0 ≤ r) (hrp : r ≤ (Nat.ceil p : ℝ)) :
    Φ y ^ r ≤ (1 + C) ^ Nat.ceil p * (1 + ‖y‖) ^ (d * Nat.ceil p) := by
  let A : ℝ := 1 + ‖y‖
  let Q : ℝ := (1 + C) * A ^ d
  have hA : 1 ≤ A := by change 1 ≤ 1 + ‖y‖; linarith [norm_nonneg y]
  have hAd : 1 ≤ A ^ d := one_le_pow₀ hA
  have hPhi : Φ y ≤ C * A ^ d := by
    dsimp [A]
    exact (le_abs_self _).trans (hvalue y)
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact one_le_mul_of_one_le_of_one_le (by linarith) hAd
  have hPhiQ : Φ y ≤ Q := by
    dsimp [Q]
    exact hPhi.trans (by gcongr; linarith)
  calc
    Φ y ^ r ≤ Q ^ r := Real.rpow_le_rpow (hΦnonneg y) hPhiQ hr
    _ ≤ Q ^ (Nat.ceil p : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ hrp
    _ = (1 + C) ^ Nat.ceil p * A ^ (d * Nat.ceil p) := by
      dsimp [Q]
      rw [Real.rpow_natCast, mul_pow, pow_mul]
    _ = (1 + C) ^ Nat.ceil p * (1 + ‖y‖) ^ (d * Nat.ceil p) := by
      rfl

/-- The Hessian trace of the base observable, weighted by the power-rule factor. -/
noncomputable def gaussianSeriesPowerHessianTrace {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (x : E) (t : ℝ) (ω : ℕ → ℝ) : ℝ :=
  ∑' j, secondDirectionalDerivative Φ (gaussianSeriesHeatArgument hA T x t ω) (T (v j))

/-- The squared-gradient trace of the base observable, weighted by the power-rule factor. -/
noncomputable def gaussianSeriesPowerGradientSquareTrace {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [OpensMeasurableSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (x : E) (t : ℝ) (ω : ℕ → ℝ) : ℝ :=
  ∑' j, (fderiv ℝ Φ (gaussianSeriesHeatArgument hA T x t ω) (T (v j))) ^ 2

/-- The bracket series is absolutely convergent pointwise, by the square-summable mapped
directions and the polynomial bound on `DΦ`. -/
theorem summable_gaussianSeriesPowerGradientSquareTerms {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    {Φ : E → ℝ} (hΦ : HasPolynomiallyBoundedC2Derivatives Φ) (y : E) :
    Summable (fun j => (fderiv ℝ Φ y (T (v j))) ^ 2) := by
  rcases hΦ with ⟨_, C, hC, d, _, hfirst, _⟩
  let A : ℝ := 1 + ‖y‖
  let K : ℝ := C ^ 2 * A ^ (2 * d)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hdir := summable_sq_norm_gaussianDirections hA T
  apply (hdir.mul_left K).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hD : |fderiv ℝ Φ y (T (v j))| ≤ C * A ^ d * ‖T (v j)‖ := by
    calc
      |fderiv ℝ Φ y (T (v j))| = ‖fderiv ℝ Φ y (T (v j))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ Φ y‖ * ‖T (v j)‖ := (fderiv ℝ Φ y).le_opNorm _
      _ ≤ C * A ^ d * ‖T (v j)‖ := by
        simpa [A] using mul_le_mul_of_nonneg_right (hfirst y) (norm_nonneg _)
  have hDsquare : (fderiv ℝ Φ y (T (v j))) ^ 2 ≤
      (C * A ^ d * ‖T (v j)‖) ^ 2 := by
    apply (sq_le_sq).2
    simpa [abs_of_nonneg (by positivity : 0 ≤ C * A ^ d * ‖T (v j)‖)] using hD
  calc
    (fderiv ℝ Φ y (T (v j))) ^ 2 ≤
        (C * A ^ d * ‖T (v j)‖) ^ 2 := hDsquare
    _ = K * ‖T (v j)‖ ^ 2 := by dsimp [K]; ring

private lemma summable_gaussianPowerHessianTerms {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    {Φ : E → ℝ} (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (hΦnonneg : ∀ y, 0 ≤ Φ y) {p : ℝ} (hp : 2 ≤ p) (y : E) :
    Summable (fun j => p * Φ y ^ (p - 1) *
      secondDirectionalDerivative Φ y (T (v j))) := by
  rcases hΦ with ⟨_, C, hC, d, _, _, hsecond⟩
  let A : ℝ := 1 + ‖y‖
  let K : ℝ := |p| * Φ y ^ (p - 1) * C * A ^ d
  have hpow : 0 ≤ Φ y ^ (p - 1) := Real.rpow_nonneg (hΦnonneg y) (p - 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hdir := summable_sq_norm_gaussianDirections hA T
  apply (hdir.mul_left K).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hpow]
  have hsec : |secondDirectionalDerivative Φ y (T (v j))| ≤
      C * A ^ d * ‖T (v j)‖ ^ 2 := by
    have h := hsecond y (T (v j)) (T (v j))
    simpa [secondDirectionalDerivative, A, pow_two, mul_assoc] using h
  calc
    |p| * Φ y ^ (p - 1) *
        |secondDirectionalDerivative Φ y (T (v j))| ≤
      |p| * Φ y ^ (p - 1) * (C * A ^ d * ‖T (v j)‖ ^ 2) := by
        gcongr
    _ = K * ‖T (v j)‖ ^ 2 := by dsimp [K]; ring

private lemma summable_gaussianPowerGradientTerms {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    {Φ : E → ℝ} (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (hΦnonneg : ∀ y, 0 ≤ Φ y) {p : ℝ} (hp : 2 ≤ p) (y : E) :
    Summable (fun j => p * (p - 1) * Φ y ^ (p - 2) *
      (fderiv ℝ Φ y (T (v j))) ^ 2) := by
  rcases hΦ with ⟨_, C, hC, d, _, hfirst, _⟩
  let A : ℝ := 1 + ‖y‖
  let K : ℝ := |p * (p - 1)| * Φ y ^ (p - 2) * C ^ 2 * A ^ (2 * d)
  have hp2 : 0 ≤ p - 2 := by linarith
  have hpow : 0 ≤ Φ y ^ (p - 2) := Real.rpow_nonneg (hΦnonneg y) (p - 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hdir := summable_sq_norm_gaussianDirections hA T
  apply (hdir.mul_left K).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs]
  have hnorm : |p * (p - 1) * Φ y ^ (p - 2) *
      (fderiv ℝ Φ y (T (v j))) ^ 2| =
      |p * (p - 1)| * Φ y ^ (p - 2) *
        (fderiv ℝ Φ y (T (v j))) ^ 2 := by
    calc
      _ = |p * (p - 1)| * |Φ y ^ (p - 2)| *
          |(fderiv ℝ Φ y (T (v j))) ^ 2| := by rw [abs_mul, abs_mul]
      _ = _ := by
        rw [abs_of_nonneg hpow]
        rw [abs_of_nonneg (sq_nonneg (fderiv ℝ Φ y (T (v j))))]
  rw [hnorm]
  have hD : |fderiv ℝ Φ y (T (v j))| ≤ C * A ^ d * ‖T (v j)‖ := by
    calc
      |fderiv ℝ Φ y (T (v j))| = ‖fderiv ℝ Φ y (T (v j))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ Φ y‖ * ‖T (v j)‖ := (fderiv ℝ Φ y).le_opNorm _
      _ ≤ C * A ^ d * ‖T (v j)‖ := by
        simpa [A] using mul_le_mul_of_nonneg_right (hfirst y) (norm_nonneg _)
  have hDsquare : (fderiv ℝ Φ y (T (v j))) ^ 2 ≤
      (C * A ^ d * ‖T (v j)‖) ^ 2 := by
    apply (sq_le_sq).2
    simpa [abs_of_nonneg (by positivity : 0 ≤ C * A ^ d * ‖T (v j)‖)] using hD
  calc
    |p * (p - 1)| * Φ y ^ (p - 2) *
        (fderiv ℝ Φ y (T (v j))) ^ 2 ≤
      |p * (p - 1)| * Φ y ^ (p - 2) * (C * A ^ d * ‖T (v j)‖) ^ 2 := by
        gcongr
    _ = K * ‖T (v j)‖ ^ 2 := by dsimp [K]; ring

/-- Pointwise power-rule expansion of the infinite Hessian trace. The two terms are separately
absolutely summable. -/
theorem gaussianSeriesHeatTrace_rpow {V E : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    [OpensMeasurableSpace V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℕ → V} (hA : Summable (fun j => ‖v j‖ ^ 2)) (T : V →L[ℝ] E)
    (Φ : E → ℝ) (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (hΦnonneg : ∀ y, 0 ≤ Φ y) {p : ℝ} (hp : 2 ≤ p)
    (x : E) (t : ℝ) (ω : ℕ → ℝ) :
    gaussianSeriesHeatTrace hA T (fun y => Φ y ^ p) x t ω =
      p * Φ (gaussianSeriesHeatArgument hA T x t ω) ^ (p - 1) *
    gaussianSeriesPowerHessianTrace hA T Φ x t ω +
        p * (p - 1) * Φ (gaussianSeriesHeatArgument hA T x t ω) ^ (p - 2) *
          gaussianSeriesPowerGradientSquareTrace hA T Φ x t ω := by
  let y := gaussianSeriesHeatArgument hA T x t ω
  have h1 := summable_gaussianPowerHessianTerms hA T hΦ hΦnonneg hp y
  have h2 := summable_gaussianPowerGradientTerms hA T hΦ hΦnonneg hp y
  change (∑' j, secondDirectionalDerivative (fun z => Φ z ^ p) y (T (v j))) = _
  calc
    _ = ∑' j, (p * Φ y ^ (p - 1) * secondDirectionalDerivative Φ y (T (v j)) +
          p * (p - 1) * Φ y ^ (p - 2) * (fderiv ℝ Φ y (T (v j))) ^ 2) := by
      apply tsum_congr
      intro j
      exact secondDirectionalDerivative_rpow_comp hΦ.1 hp y (T (v j))
    _ = (∑' j, p * Φ y ^ (p - 1) * secondDirectionalDerivative Φ y (T (v j))) +
          ∑' j, p * (p - 1) * Φ y ^ (p - 2) *
            (fderiv ℝ Φ y (T (v j))) ^ 2 := Summable.tsum_add h1 h2
    _ = p * Φ y ^ (p - 1) * gaussianSeriesPowerHessianTrace hA T Φ x t ω +
          p * (p - 1) * Φ y ^ (p - 2) * gaussianSeriesPowerGradientSquareTrace hA T Φ x t ω := by
      simp [gaussianSeriesPowerHessianTrace, gaussianSeriesPowerGradientSquareTrace, y,
        tsum_mul_left]

/-- A nonnegative polynomially controlled `C²` observable stays in the same class after a real
power `p ≥ 2`. -/
theorem hasPolynomiallyBoundedC2Derivatives_rpow {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : HasPolynomiallyBoundedC2Derivatives Φ)
    (hΦnonneg : ∀ y, 0 ≤ Φ y) {p : ℝ} (hp : 2 ≤ p) :
    HasPolynomiallyBoundedC2Derivatives (fun y => Φ y ^ p) := by
  rcases hΦ with ⟨hC2, C, hC, d, hvalue, hfirst, hsecond⟩
  let N : ℕ := Nat.ceil p
  let D : ℕ := d * (N + 2)
  let Qn : ℝ := (1 + C) ^ N
  let K : ℝ := (1 + |p| * C + |p * (p - 1)| * C ^ 2) * Qn
  have hpN : p ≤ (N : ℝ) := by dsimp [N]; exact Nat.le_ceil p
  have hQn : 1 ≤ Qn := by
    dsimp [Qn]
    exact one_le_pow₀ (by linarith)
  have hfactor : 1 ≤ 1 + |p| * C + |p * (p - 1)| * C ^ 2 := by
    have h₁ : 0 ≤ |p| * C := mul_nonneg (abs_nonneg p) hC
    have h₂ : 0 ≤ |p * (p - 1)| * C ^ 2 :=
      mul_nonneg (abs_nonneg (p * (p - 1))) (sq_nonneg C)
    linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKq : Qn ≤ K := by
    dsimp [K]
    calc
      Qn = 1 * Qn := by ring
      _ ≤ (1 + |p| * C + |p * (p - 1)| * C ^ 2) * Qn :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
  have hKfirst : |p| * C * Qn ≤ K := by
    dsimp [K]
    calc
      |p| * C * Qn ≤ (1 + |p| * C + |p * (p - 1)| * C ^ 2) * Qn := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have h₂ : 0 ≤ |p * (p - 1)| * C ^ 2 :=
          mul_nonneg (abs_nonneg (p * (p - 1))) (sq_nonneg C)
        linarith
      _ = (1 + |p| * C + |p * (p - 1)| * C ^ 2) * Qn := rfl
  have hKsecond :
      (|p| * C + |p * (p - 1)| * C ^ 2) * Qn ≤ K := by
    dsimp [K]
    calc
      (|p| * C + |p * (p - 1)| * C ^ 2) * Qn ≤
          (1 + |p| * C + |p * (p - 1)| * C ^ 2) * Qn := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
      _ = (1 + |p| * C + |p * (p - 1)| * C ^ 2) * Qn := rfl
  have hD : d * N + 2 * d = D := by
    dsimp [D]
    rw [Nat.mul_add]
    omega
  have hD0 : d * N ≤ D := by
    dsimp [D]
    rw [Nat.mul_add]
    omega
  have hD1 : d * N + d ≤ D := by
    dsimp [D]
    rw [Nat.mul_add]
    omega
  have hpow (y : E) (r : ℝ) (hr : 0 ≤ r) (hrp : r ≤ (N : ℝ)) :
      Φ y ^ r ≤ Qn * (1 + ‖y‖) ^ (d * N) := by
    dsimp [N, Qn]
    exact rpow_le_polynomial_envelope hΦnonneg hC d hvalue y r hr hrp
  have hC2pow : ContDiff ℝ 2 (fun y => Φ y ^ p) := by
    exact hC2.rpow_const_of_le (by exact_mod_cast hp)
  refine ⟨hC2pow, K, hK, D, ?_, ?_, ?_⟩
  · intro y
    have hp0 : 0 ≤ p := by linarith
    rw [abs_of_nonneg (Real.rpow_nonneg (hΦnonneg y) p)]
    have henv := hpow y p hp0 (by linarith)
    calc
      Φ y ^ p ≤ Qn * (1 + ‖y‖) ^ (d * N) := henv
      _ ≤ Qn * (1 + ‖y‖) ^ D := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by nlinarith [norm_nonneg y]) hD0) (by positivity)
      _ ≤ K * (1 + ‖y‖) ^ D :=
        mul_le_mul_of_nonneg_right hKq (by positivity)
  · intro y
    rw [fderiv_rpow_comp hC2 hp y]
    have hp1 : 0 ≤ p - 1 := by linarith
    have henv := hpow y (p - 1) hp1 (by linarith)
    have hcoeff : |p| * C * Qn ≤ K := hKfirst
    calc
      ‖(p * Φ y ^ (p - 1)) • fderiv ℝ Φ y‖ =
          |p| * Φ y ^ (p - 1) * ‖fderiv ℝ Φ y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (hΦnonneg y) (p - 1))]
      _ ≤ |p| * (Qn * (1 + ‖y‖) ^ (d * N)) *
          (C * (1 + ‖y‖) ^ d) := by
        gcongr
        exact hfirst y
      _ = (|p| * C * Qn) * (1 + ‖y‖) ^ (d * N + d) := by
        rw [pow_add]
        ring
      _ ≤ (|p| * C * Qn) * (1 + ‖y‖) ^ D := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by nlinarith [norm_nonneg y]) hD1) (by positivity)
      _ ≤ K * (1 + ‖y‖) ^ D :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
  · intro y u w
    rw [fderiv_fderiv_rpow_comp hC2 hp y u w]
    let A : ℝ := 1 + ‖y‖
    have hA : 1 ≤ A := by change 1 ≤ 1 + ‖y‖; linarith [norm_nonneg y]
    have hA0 : 0 ≤ A := le_trans (by norm_num) hA
    have hp1 : 0 ≤ p - 1 := by linarith
    have hp2 : 0 ≤ p - 2 := by linarith
    have henv1 := hpow y (p - 1) hp1 (by linarith)
    have henv2 := hpow y (p - 2) hp2 (by linarith)
    have hDu : |fderiv ℝ Φ y u| ≤ C * A ^ d * ‖u‖ := by
      calc
        |fderiv ℝ Φ y u| = ‖fderiv ℝ Φ y u‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ Φ y‖ * ‖u‖ := (fderiv ℝ Φ y).le_opNorm _
        _ ≤ C * A ^ d * ‖u‖ := by
          simpa [A] using mul_le_mul_of_nonneg_right (hfirst y) (norm_nonneg u)
    have hDw : |fderiv ℝ Φ y w| ≤ C * A ^ d * ‖w‖ := by
      calc
        |fderiv ℝ Φ y w| = ‖fderiv ℝ Φ y w‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ Φ y‖ * ‖w‖ := (fderiv ℝ Φ y).le_opNorm _
        _ ≤ C * A ^ d * ‖w‖ := by
          simpa [A] using mul_le_mul_of_nonneg_right (hfirst y) (norm_nonneg w)
    have hsecond' :
        |fderiv ℝ (fun z => fderiv ℝ Φ z w) y u| ≤ C * A ^ d * ‖u‖ * ‖w‖ := by
      simpa [A] using hsecond y u w
    have hterm₁ :
        |p * Φ y ^ (p - 1) * fderiv ℝ (fun z => fderiv ℝ Φ z w) y u| ≤
          (|p| * C * Qn) * A ^ (d * N + d) * ‖u‖ * ‖w‖ := by
      calc
        _ = |p| * Φ y ^ (p - 1) *
            |fderiv ℝ (fun z => fderiv ℝ Φ z w) y u| := by
              rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (hΦnonneg y) _)]
        _ ≤ |p| * (Qn * A ^ (d * N)) *
            (C * A ^ d * ‖u‖ * ‖w‖) := by
              gcongr
        _ = _ := by rw [pow_add]; ring
    have hterm₂ :
        |p * (p - 1) * Φ y ^ (p - 2) * (fderiv ℝ Φ y u) *
            (fderiv ℝ Φ y w)| ≤
          (|p * (p - 1)| * C ^ 2 * Qn) * A ^ (d * N + 2 * d) * ‖u‖ * ‖w‖ := by
      calc
        _ = |p * (p - 1)| * Φ y ^ (p - 2) *
            |fderiv ℝ Φ y u| * |fderiv ℝ Φ y w| := by
              rw [abs_mul, abs_mul, abs_mul,
                abs_of_nonneg (Real.rpow_nonneg (hΦnonneg y) _)]
        _ ≤ |p * (p - 1)| * (Qn * A ^ (d * N)) *
            (C * A ^ d * ‖u‖) * (C * A ^ d * ‖w‖) := by
              gcongr
        _ = _ := by rw [pow_add]; ring
    have hcoefsum : |p| * C * Qn + |p * (p - 1)| * C ^ 2 * Qn ≤ K := by
      simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using hKsecond
    have hpow1D : A ^ (d * N + d) ≤ A ^ D := pow_le_pow_right₀ hA hD1
    have hpow2D : A ^ (d * N + 2 * d) ≤ A ^ D := by rw [hD]
    have hnormprod : 0 ≤ ‖u‖ * ‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    let c₁ : ℝ := |p| * C * Qn
    let c₂ : ℝ := |p * (p - 1)| * C ^ 2 * Qn
    calc
      _ ≤ |p * Φ y ^ (p - 1) * fderiv ℝ (fun z => fderiv ℝ Φ z w) y u| +
          |p * (p - 1) * Φ y ^ (p - 2) * (fderiv ℝ Φ y u) *
            (fderiv ℝ Φ y w)| := abs_add_le _ _
      _ ≤ (|p| * C * Qn) * A ^ (d * N + d) * ‖u‖ * ‖w‖ +
          (|p * (p - 1)| * C ^ 2 * Qn) * A ^ (d * N + 2 * d) * ‖u‖ * ‖w‖ :=
        add_le_add hterm₁ hterm₂
      _ ≤ (c₁ + c₂) * A ^ D * ‖u‖ * ‖w‖ := by
        calc
          _ = (c₁ * A ^ (d * N + d) + c₂ * A ^ (d * N + 2 * d)) *
                (‖u‖ * ‖w‖) := by dsimp [c₁, c₂]; ring
          _ ≤ (c₁ * A ^ D + c₂ * A ^ D) * (‖u‖ * ‖w‖) := by
                exact mul_le_mul_of_nonneg_right
                  (add_le_add
                    (mul_le_mul_of_nonneg_left hpow1D (by positivity))
                    (mul_le_mul_of_nonneg_left hpow2D (by positivity))) hnormprod
          _ = (c₁ + c₂) * A ^ D * ‖u‖ * ‖w‖ := by ring
      _ ≤ K * A ^ D * ‖u‖ * ‖w‖ := by
        have hc : (c₁ + c₂) * A ^ D ≤ K * A ^ D := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          simpa [c₁, c₂] using hcoefsum
        calc
          _ = ((c₁ + c₂) * A ^ D) * (‖u‖ * ‖w‖) := by ring
          _ ≤ (K * A ^ D) * (‖u‖ * ‖w‖) :=
            mul_le_mul_of_nonneg_right hc hnormprod
          _ = K * A ^ D * ‖u‖ * ‖w‖ := by ring
      _ = K * (1 + ‖y‖) ^ D * ‖u‖ * ‖w‖ := by dsimp [A]

end ASDExplicitGamma.Gaussian
