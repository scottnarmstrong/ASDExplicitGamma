module

public import ASDExplicitGamma.Gaussian.BilinearCovariance
public import ASDExplicitGamma.Gaussian.PolynomialTests
public import ASDExplicitGamma.Gaussian.FiniteHeat
public import ASDExplicitGamma.Gaussian.SeriesHeat
public import ASDExplicitGamma.Gaussian.SupMeanFiniteConcentration
public import ASDExplicitGamma.Gaussian.DerivativeLawFamilies
public import ASDExplicitGamma.Gaussian.RealizationSeries

/-! Finite-dimensional Gaussian quadratic-form moments for the native heat input. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Filter ASDExplicitGamma.Gaussian
open scoped RealInnerProductSpace Topology

/-- The normalized squared norm as a bounded quadratic form. -/
noncomputable def nativeGaussianCenterBilinear {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (d : ℕ) :
    E →L[ℝ] E →L[ℝ] ℝ := (1 / (d : ℝ)) • innerSL ℝ

/-- The normalized squared Euclidean norm used for a Gaussian center vector. -/
noncomputable def nativeGaussianCenterQuadratic {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (d : ℕ) (x : E) : ℝ :=
  nativeGaussianCenterBilinear d x x

theorem nativeGaussianCenterQuadratic_c2 {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (d : ℕ) :
    HasPolynomiallyBoundedC2Derivatives (E := E) (nativeGaussianCenterQuadratic d) := by
  exact bilinear_diagonal_polynomial (nativeGaussianCenterBilinear (E := E) d)

theorem nativeGaussianCenterQuadratic_fderiv {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (d : ℕ) (x w : E) :
    fderiv ℝ (nativeGaussianCenterQuadratic d) x w =
      (2 / (d : ℝ)) * inner ℝ x w := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := nativeGaussianCenterBilinear (E := E) d
  have hB (y z : E) : B y z = (1 / (d : ℝ)) * inner ℝ y z := by
    change (1 / (d : ℝ)) * ((innerSL ℝ y) z) = _
    rw [innerSL_apply_apply]
  have hsym : B.flip = B := by
    ext y z
    change B z y = B y z
    rw [hB, hB, real_inner_comm]
  have hderiv (y : E) :
      fderiv ℝ (nativeGaussianCenterQuadratic d) y = B y + B.flip y := by
    convert (B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)).fderiv
      using 1 <;> ext u <;> rfl
  rw [hderiv x, hsym, add_apply, hB]
  ring

theorem nativeGaussianCenterQuadratic_secondDirectional {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (d : ℕ) (x w : E) :
    secondDirectionalDerivative (nativeGaussianCenterQuadratic d) x w =
      (2 / (d : ℝ)) * ‖w‖ ^ 2 := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := nativeGaussianCenterBilinear (E := E) d
  have hB (y z : E) : B y z = (1 / (d : ℝ)) * inner ℝ y z := by
    change (1 / (d : ℝ)) * ((innerSL ℝ y) z) = _
    rw [innerSL_apply_apply]
  have hsym : B.flip = B := by
    ext y z
    change B z y = B y z
    rw [hB, hB, real_inner_comm]
  have hderiv (y : E) :
      fderiv ℝ (nativeGaussianCenterQuadratic d) y = B y + B.flip y := by
    convert (B.hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)).fderiv
      using 1 <;> ext u <;> rfl
  have hsecond (y u v : E) :
      fderiv ℝ (fun z => fderiv ℝ (nativeGaussianCenterQuadratic d) z v) y u =
        B u v + B v u := by
    simp only [hderiv, add_apply, ContinuousLinearMap.flip_apply]
    change fderiv ℝ (fun z => B.flip v z + B v z) y u = _
    exact congrArg (fun L : E →L[ℝ] ℝ => L u)
      (((B.flip v).hasFDerivAt (x := y)).add (B v).hasFDerivAt).fderiv
  rw [secondDirectionalDerivative, hsecond x w w]
  rw [hB]
  rw [real_inner_self_eq_norm_sq]
  ring

/-- At dimension one, the normalized quadratic form is the squared norm. -/
theorem nativeGaussianCenterQuadratic_one {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) :
    nativeGaussianCenterQuadratic (E := E) 1 x = ‖x‖ ^ 2 := by
  simp only [nativeGaussianCenterQuadratic, nativeGaussianCenterBilinear, smul_apply]
  rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  norm_num [real_inner_self_eq_norm_sq]

/-- Homogeneity of the normalized center quadratic form. -/
theorem nativeGaussianCenterQuadratic_smul {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (c : ℝ) (x : E) :
    nativeGaussianCenterQuadratic (E := E) 1 (c • x) =
      c ^ 2 * nativeGaussianCenterQuadratic 1 x := by
  rw [nativeGaussianCenterQuadratic_one, nativeGaussianCenterQuadratic_one, norm_smul]
  rw [Real.norm_eq_abs, mul_pow, sq_abs]

/-- The Hessian of a natural power, evaluated twice in one direction. -/
theorem nativeHeat_secondDirectional_natPower {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (m : ℕ) (hm : 2 ≤ m) (x v : E) :
    secondDirectionalDerivative (fun z => f z ^ m) x v =
      (m : ℝ) * f x ^ (m - 1) * secondDirectionalDerivative f x v +
        (m : ℝ) * (m - 1 : ℝ) * f x ^ (m - 2) * (fderiv ℝ f x v) ^ 2 := by
  have hfDiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hpowDer (y : E) : fderiv ℝ (fun z => f z ^ m) y =
      ((m : ℝ) * f y ^ (m - 1)) • fderiv ℝ f y := by
    change fderiv ℝ (f ^ m) y = _
    rw [fderiv_pow m (hfDiff y)]
    simp
  have hfun : (fun z => fderiv ℝ (fun y => f y ^ m) z v) =
      fun z => (m : ℝ) * f z ^ (m - 1) * fderiv ℝ f z v := by
    funext z
    rw [hpowDer]
    simp [smul_apply, smul_eq_mul]
  have hA : HasFDerivAt (fun z => f z ^ (m - 1))
      ((((m - 1 : ℕ) : ℝ) * f x ^ (m - 2)) • fderiv ℝ f x) x := by
    have hm' : 1 ≤ m - 1 := by omega
    have hsub : m - 1 - 1 = m - 2 := by omega
    have h := ((hfDiff x).pow (m - 1)).hasFDerivAt
    rw [fderiv_pow (m - 1) (hfDiff x)] at h
    rw [show (m - 1 - 1) = m - 2 from hsub] at h
    change HasFDerivAt (f ^ (m - 1)) _ x
    simpa [Nat.cast_sub hm'] using h
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hEval := hf.contDiff_fderiv_apply (m := 1)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hpair : ContDiff ℝ 1 (fun z : E => (z, v)) := contDiff_id.prodMk contDiff_const
  let B : E → ℝ := fun z => fderiv ℝ f z v
  have hB : ContDiff ℝ 1 B := by
    simpa [B, Function.comp_def] using hEval.comp hpair
  have hBder : HasFDerivAt B (fderiv ℝ B x) x := (hB.differentiable_one x).hasFDerivAt
  have hmul := (hA.mul hBder).const_mul (m : ℝ)
  have hprod := congrArg (fun L : E →L[ℝ] ℝ => L v) hmul.fderiv
  have hEq : fderiv ℝ (fun z => (m : ℝ) * f z ^ (m - 1) * fderiv ℝ f z v) x v =
      (m : ℝ) * ((m - 1 : ℕ) : ℝ) * f x ^ (m - 2) *
          (fderiv ℝ f x v) ^ 2 +
        (m : ℝ) * f x ^ (m - 1) * fderiv ℝ B x v := by
    convert hprod using 1 <;>
      (simp [B, smul_apply, smul_eq_mul, mul_assoc, mul_left_comm] <;> try ring)
  calc
    secondDirectionalDerivative (fun z => f z ^ m) x v =
        fderiv ℝ (fun z => fderiv ℝ (fun y => f y ^ m) z v) x v := rfl
    _ = fderiv ℝ (fun z => (m : ℝ) * f z ^ (m - 1) * fderiv ℝ f z v) x v := by
      exact congrArg (fun g : E → ℝ => fderiv ℝ g x v) hfun
    _ = (m : ℝ) * ((m - 1 : ℕ) : ℝ) * f x ^ (m - 2) *
          (fderiv ℝ f x v) ^ 2 +
        (m : ℝ) * f x ^ (m - 1) * fderiv ℝ B x v := hEq
    _ = (m : ℝ) * f x ^ (m - 1) * secondDirectionalDerivative f x v +
          (m : ℝ) * (m - 1 : ℝ) * f x ^ (m - 2) *
            (fderiv ℝ f x v) ^ 2 := by
      change (m : ℝ) * ((m - 1 : ℕ) : ℝ) * f x ^ (m - 2) *
          (fderiv ℝ f x v) ^ 2 +
        (m : ℝ) * f x ^ (m - 1) *
          fderiv ℝ (fun z => fderiv ℝ f z v) x v =
        (m : ℝ) * f x ^ (m - 1) *
          fderiv ℝ (fun z => fderiv ℝ f z v) x v +
        (m : ℝ) * (m - 1 : ℝ) * f x ^ (m - 2) *
          (fderiv ℝ f x v) ^ 2
      have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ m)]
        norm_num
      rw [hmcast]
      ring

/-- The `k`th quadratic moment of a finite Gaussian linear image, in its standard
coordinate representation. -/
noncomputable def nativeHeatCenterMoment {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (A : Fin n → E) (k : ℕ) : ℝ :=
  ∫ ξ, nativeGaussianCenterQuadratic 1 (∑ i, ξ i • A i) ^ k
    ∂(standardGaussianPi n)

private theorem nativeHeat_coordinateDerivative_affine {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {G : E → ℝ}
    (hG : ContDiff ℝ 1 G) (A : (Fin n → ℝ) →L[ℝ] E) (x : E)
    (i : Fin n) (ξ : Fin n → ℝ) :
    coordinateDerivative (fun y => G (x + A y)) i ξ =
      fderiv ℝ G (x + A ξ) (A (Pi.single i (1 : ℝ))) := by
  have houter := (hG.differentiable_one (x + A ξ)).hasFDerivAt
  have hinner : HasFDerivAt (fun y : Fin n → ℝ => x + A y) A ξ :=
    A.hasFDerivAt.const_add x
  have hcomp := houter.comp ξ hinner
  have hderiv := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ =>
    L (Pi.single i (1 : ℝ))) hcomp.fderiv
  simpa [Function.comp_def, coordinateDerivative, ContinuousLinearMap.comp_apply] using hderiv

private theorem nativeHeat_secondCoordinate_covarianceFactorObservable {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Φ : E → ℝ}
    (hΦ : ContDiff ℝ 2 Φ) (x : E) (A : Fin n → E) (i : Fin n)
    (ξ : Fin n → ℝ) :
    coordinateDerivative (coordinateDerivative (covarianceFactorObservable Φ x A) i) i ξ =
      secondDirectionalDerivative Φ (x + covarianceFactorMap A ξ) (A i) := by
  let L : (Fin n → ℝ) →L[ℝ] E := covarianceFactorMap A
  have hΦ1 : ContDiff ℝ 1 Φ := hΦ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hG : ContDiff ℝ 1 (fun y : E => fderiv ℝ Φ y (A i)) := by
    have h := hΦ.contDiff_fderiv_apply (m := 1)
      (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    have hpair : ContDiff ℝ 1 (fun y : E => (y, A i)) :=
      contDiff_id.prodMk contDiff_const
    simpa [Function.comp_def] using h.comp hpair
  have hpartial : coordinateDerivative (covarianceFactorObservable Φ x A) i =
      fun η => fderiv ℝ Φ (x + L η) (A i) := by
    funext η
    change coordinateDerivative (fun y => Φ (x + L y)) i η = _
    have houter := (hΦ1.differentiable_one (x + L η)).hasFDerivAt
    have hinner : HasFDerivAt (fun y : Fin n → ℝ => x + L y) L η :=
      L.hasFDerivAt.const_add x
    have hcomp := houter.comp η hinner
    have hderiv := congrArg (fun D : (Fin n → ℝ) →L[ℝ] ℝ =>
      D (Pi.single i (1 : ℝ))) hcomp.fderiv
    have hsingle : L (Pi.single i (1 : ℝ)) = A i := by
      rw [covarianceFactorMap_apply_local]
      simp
    simpa [covarianceFactorObservable, Function.comp_def, coordinateDerivative,
      ContinuousLinearMap.comp_apply, hsingle] using hderiv
  rw [hpartial]
  change coordinateDerivative (fun η => fderiv ℝ Φ (x + L η) (A i)) i ξ = _
  rw [nativeHeat_coordinateDerivative_affine hG L x i ξ]
  have hsingle : L (Pi.single i (1 : ℝ)) = A i := by
    rw [covarianceFactorMap_apply_local]
    simp
  rw [hsingle]
  rfl

/-- Gaussian integration by parts gives the covariance trace/spectral recurrence
for every positive quadratic moment. The hypotheses are the actual covariance
trace and operator bounds of the finite Gaussian center vector. -/
theorem nativeHeatCenterMoment_step {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
    (A : Fin n → E) (V L : ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hV : ∑ i, ‖A i‖ ^ 2 ≤ V)
    (hL : ∀ x : E, ∑ i, (inner ℝ x (A i)) ^ 2 ≤ L * ‖x‖ ^ 2) :
    nativeHeatCenterMoment A (k + 1) ≤
      (V + 2 * (k : ℝ) * L) * nativeHeatCenterMoment A k := by
  let Q : E → ℝ := nativeGaussianCenterQuadratic 1
  let Φ : E → ℝ := fun x => Q x ^ (k + 1)
  let F : (Fin n → ℝ) → ℝ := covarianceFactorObservable Φ 0 A
  have hQ : HasPolynomiallyBoundedC2Derivatives Q := nativeGaussianCenterQuadratic_c2 1
  have hΦ : HasPolynomiallyBoundedC2Derivatives Φ := by
    simpa [Q, Φ] using c2_polynomial_pow hQ (k + 1)
  have hGrowth : HasPolynomiallyBoundedSecondCoordinateDerivatives F := by
    simpa [F, Φ] using
      hasPolynomiallyBoundedSecondCoordinateDerivatives_covarianceFactorObservable
        hΦ 0 A
  let H : ℝ → ℝ := fun t => heatAverage F 0 t
  have hheat := hasDerivAt_covarianceFactorObservable hΦ.1 0 A hGrowth
    (t := 1) (by norm_num)
  have hhom (c : ℝ) (x : E) : Q (c • x) = c ^ 2 * Q x := by
    simpa [Q] using nativeGaussianCenterQuadratic_smul c x
  have hvalue (s : ℝ) (hs : 0 ≤ s) :
      H s = s ^ (k + 1) * nativeHeatCenterMoment A (k + 1) := by
    unfold H heatAverage shiftAverage F covarianceFactorObservable
    have hmap (ξ : Fin n → ℝ) :
        covarianceFactorMap A (Real.sqrt s • ξ) =
          Real.sqrt s • covarianceFactorMap A ξ := by
      exact (covarianceFactorMap A).map_smul _ _
    calc
      (∫ ξ, Φ (0 + covarianceFactorMap A (0 + Real.sqrt s • ξ))
          ∂(standardGaussianPi n)) =
          ∫ ξ, s ^ (k + 1) * Q (covarianceFactorMap A ξ) ^ (k + 1)
            ∂(standardGaussianPi n) := by
              apply integral_congr_ae
              filter_upwards [] with ξ
              simp only [zero_add]
              change Q (covarianceFactorMap A (Real.sqrt s • ξ)) ^ (k + 1) = _
              rw [hmap, hhom, Real.sq_sqrt hs, mul_pow]
      _ = s ^ (k + 1) * nativeHeatCenterMoment A (k + 1) := by
        rw [integral_const_mul]
        apply congrArg (fun z : ℝ => s ^ (k + 1) * z)
        change (∫ ξ, Q (covarianceFactorMap A ξ) ^ (k + 1)
            ∂(standardGaussianPi n)) =
          ∫ ξ, Q (∑ i, ξ i • A i) ^ (k + 1) ∂(standardGaussianPi n)
        apply integral_congr_ae
        filter_upwards [] with ξ
        rw [covarianceFactorMap_apply_local]
  have hevent : H =ᶠ[𝓝 (1 : ℝ)]
      (fun s => s ^ (k + 1) * nativeHeatCenterMoment A (k + 1)) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 2)] with s hs
    exact hvalue s hs.1.le
  have hheatH : HasDerivAt H
      ((1 / 2 : ℝ) * ∫ ξ, ∑ i, secondDirectionalDerivative Φ
        (0 + Real.sqrt 1 • ∑ j, ξ j • A j) (A i)
        ∂(standardGaussianPi n)) 1 := by
    simpa [H, F] using hheat
  have hderiv := hheatH.congr_of_eventuallyEq hevent.symm
  have hpow : HasDerivAt
      (fun s : ℝ => s ^ (k + 1) * nativeHeatCenterMoment A (k + 1))
      ((k + 1 : ℝ) * (1 : ℝ) ^ k * nativeHeatCenterMoment A (k + 1)) 1 := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id (1 : ℝ)).pow (k + 1)).mul_const
      (nativeHeatCenterMoment A (k + 1))
  have hcoeff := hderiv.unique hpow
  have hheatIdentity :
      (1 / 2 : ℝ) * ∫ ξ, ∑ i, secondDirectionalDerivative Φ
        (Real.sqrt (1 : ℝ) • (∑ j, ξ j • A j)) (A i)
        ∂(standardGaussianPi n) =
        (k + 1 : ℝ) * nativeHeatCenterMoment A (k + 1) := by
    simpa [H, Real.sqrt_one, one_smul, zero_add] using hcoeff
  have hformula (x : E) (i : Fin n) :
      secondDirectionalDerivative Φ x (A i) =
        2 * (k + 1 : ℝ) * Q x ^ k * ‖A i‖ ^ 2 +
          4 * (k + 1 : ℝ) * (k : ℝ) * Q x ^ (k - 1) *
            (inner ℝ x (A i)) ^ 2 := by
    have hm := nativeHeat_secondDirectional_natPower hQ.1 (k + 1)
      (by omega) x (A i)
    rw [show k + 1 - 1 = k by omega,
      show k + 1 - 2 = k - 1 by omega] at hm
    dsimp [Φ, Q]
    rw [hm, nativeGaussianCenterQuadratic_secondDirectional,
      nativeGaussianCenterQuadratic_fderiv]
    norm_num
    ring
  have hQnonneg (x : E) : 0 ≤ Q x := by
    change 0 ≤ nativeGaussianCenterQuadratic 1 x
    rw [nativeGaussianCenterQuadratic_one]
    positivity
  have hlapBound (x : E) :
      (1 / 2 : ℝ) * ∑ i, secondDirectionalDerivative Φ x (A i) ≤
        (k + 1 : ℝ) * (V + 2 * (k : ℝ) * L) * Q x ^ k := by
    have hqx := hQnonneg x
    have htraceCoeff : 0 ≤ (k + 1 : ℝ) * Q x ^ k := by positivity
    have hspectralCoeff : 0 ≤ 2 * (k + 1 : ℝ) * (k : ℝ) * Q x ^ (k - 1) := by
      positivity
    have hsumFormula :
        (1 / 2 : ℝ) * ∑ i, secondDirectionalDerivative Φ x (A i) =
          ((k + 1 : ℝ) * Q x ^ k) * ∑ i, ‖A i‖ ^ 2 +
            (2 * (k + 1 : ℝ) * (k : ℝ) * Q x ^ (k - 1)) *
              ∑ i, (inner ℝ x (A i)) ^ 2 := by
      simp_rw [hformula]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      ring
    have hspec := hL x
    have hnormSq : ‖x‖ ^ 2 = Q x := by
      change ‖x‖ ^ 2 = nativeGaussianCenterQuadratic 1 x
      rw [nativeGaussianCenterQuadratic_one]
    calc
      (1 / 2 : ℝ) * ∑ i, secondDirectionalDerivative Φ x (A i) =
          ((k + 1 : ℝ) * Q x ^ k) * ∑ i, ‖A i‖ ^ 2 +
            (2 * (k + 1 : ℝ) * (k : ℝ) * Q x ^ (k - 1)) *
              ∑ i, (inner ℝ x (A i)) ^ 2 := hsumFormula
      _ ≤ ((k + 1 : ℝ) * Q x ^ k) * V +
            (2 * (k + 1 : ℝ) * (k : ℝ) * Q x ^ (k - 1)) *
              (L * ‖x‖ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hV htraceCoeff)
          (mul_le_mul_of_nonneg_left hspec hspectralCoeff)
      _ = (k + 1 : ℝ) * (V + 2 * (k : ℝ) * L) * Q x ^ k := by
        rw [hnormSq]
        have hpow : Q x ^ (k - 1) * Q x = Q x ^ k := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]
        calc
          (k + 1 : ℝ) * Q x ^ k * V +
              2 * (k + 1 : ℝ) * (k : ℝ) * Q x ^ (k - 1) * (L * Q x) =
              (k + 1 : ℝ) * (V * Q x ^ k +
                2 * (k : ℝ) * L * (Q x ^ (k - 1) * Q x)) := by ring
          _ = (k + 1 : ℝ) * (V + 2 * (k : ℝ) * L) * Q x ^ k := by
            rw [hpow]
            ring
  obtain ⟨C, hC, d, hvalueBound, hfirst, hsecond⟩ := hGrowth.2
  let lap : (Fin n → ℝ) → ℝ := fun ξ =>
    ∑ i, coordinateDerivative (coordinateDerivative F i) i ξ
  have hlapContinuous (i : Fin n) :
      Continuous (fun ξ : Fin n → ℝ =>
        coordinateDerivative (coordinateDerivative F i) i ξ) := by
    have heval := nativeHeat_secondCoordinate_covarianceFactorObservable hΦ.1 0 A i
    have hmap : Continuous (fun ξ : Fin n → ℝ => covarianceFactorMap A ξ) :=
      (covarianceFactorMap A).continuous
    have hdir := continuous_secondDirectionalDerivative hΦ.1 (A i)
    have hcomp := hdir.comp hmap
    have hEq : (fun ξ : Fin n → ℝ =>
        coordinateDerivative (coordinateDerivative F i) i ξ) =
        fun ξ => secondDirectionalDerivative Φ (covarianceFactorMap A ξ) (A i) := by
      funext ξ
      have hh := heval ξ
      simpa [F, covarianceFactorObservable, zero_add] using hh
    rw [hEq]
    exact hcomp
  have hlapMeas : Measurable lap := by
    dsimp [lap]
    apply Finset.measurable_sum
    intro i hi
    exact (hlapContinuous i).measurable
  have hlapPolynomialBound (ξ : Fin n → ℝ) : |lap ξ| ≤
      (Fintype.card (Fin n) : ℝ) * C * (1 + ‖ξ‖) ^ d := by
    calc
      |lap ξ| ≤ ∑ i, |coordinateDerivative (coordinateDerivative F i) i ξ| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, C * (1 + ‖ξ‖) ^ d := by
        apply Finset.sum_le_sum
        intro i hi
        exact hsecond i i ξ
      _ = (Fintype.card (Fin n) : ℝ) * C * (1 + ‖ξ‖) ^ d := by simp [mul_assoc]
  have hlapInt : Integrable lap (standardGaussianPi n) :=
    integrable_of_pi_polynomial_bound hlapMeas (by positivity) hlapPolynomialBound
  have hlowGrowth : HasPolynomiallyBoundedC2Derivatives
      (fun x : E => Q x ^ k) := by
    simpa [Q] using c2_polynomial_pow hQ k
  have hlowCoord : HasPolynomiallyBoundedSecondCoordinateDerivatives
      (covarianceFactorObservable (fun x : E => Q x ^ k) 0 A) :=
    hasPolynomiallyBoundedSecondCoordinateDerivatives_covarianceFactorObservable
      hlowGrowth 0 A
  obtain ⟨C₀, hC₀, d₀, hlowValue, _, _⟩ := hlowCoord.2
  have hlowMeas : Measurable (fun ξ : Fin n → ℝ =>
      Q (∑ i, ξ i • A i) ^ k) := by
    have heq : (fun ξ : Fin n → ℝ => Q (∑ i, ξ i • A i) ^ k) =
        covarianceFactorObservable (fun x : E => Q x ^ k) 0 A := by
      funext ξ
      simp [covarianceFactorObservable, covarianceFactorMap_apply_local]
    rw [heq]
    exact hlowCoord.1.continuous.measurable
  have hlowInt : Integrable
      (fun ξ : Fin n → ℝ => Q (∑ i, ξ i • A i) ^ k)
      (standardGaussianPi n) := by
    apply integrable_of_pi_polynomial_bound (by fun_prop) hC₀
    intro ξ
    simpa [covarianceFactorObservable, covarianceFactorMap_apply_local] using hlowValue ξ
  have hpoint (ξ : Fin n → ℝ) :
      (1 / 2 : ℝ) * lap ξ ≤
        (k + 1 : ℝ) * (V + 2 * (k : ℝ) * L) *
          Q (∑ i, ξ i • A i) ^ k := by
    have hsum : lap ξ = ∑ i,
        secondDirectionalDerivative Φ (∑ j, ξ j • A j) (A i) := by
      dsimp [lap]
      apply Finset.sum_congr rfl
      intro i hi
      rw [nativeHeat_secondCoordinate_covarianceFactorObservable hΦ.1 0 A i ξ]
      rw [zero_add, covarianceFactorMap_apply_local]
    rw [hsum]
    exact hlapBound (∑ j, ξ j • A j)
  have hint := integral_mono (hlapInt.const_mul (1 / 2 : ℝ))
    (hlowInt.const_mul ((k + 1 : ℝ) * (V + 2 * (k : ℝ) * L))) hpoint
  have hupper :
      (1 / 2 : ℝ) * ∫ ξ, lap ξ ∂(standardGaussianPi n) ≤
        ((k + 1 : ℝ) * (V + 2 * (k : ℝ) * L)) *
          nativeHeatCenterMoment A k := by
    calc
      (1 / 2 : ℝ) * ∫ ξ, lap ξ ∂(standardGaussianPi n) =
          ∫ ξ, (1 / 2 : ℝ) * lap ξ ∂(standardGaussianPi n) := by
            rw [integral_const_mul]
      _ ≤ ∫ ξ, ((k + 1 : ℝ) * (V + 2 * (k : ℝ) * L)) *
            Q (∑ i, ξ i • A i) ^ k ∂(standardGaussianPi n) := hint
      _ = ((k + 1 : ℝ) * (V + 2 * (k : ℝ) * L)) *
            nativeHeatCenterMoment A k := by
            rw [integral_const_mul]
            rfl
  have hheatLap : (1 / 2 : ℝ) * ∫ ξ, ∑ i, secondDirectionalDerivative Φ
      (Real.sqrt (1 : ℝ) • (∑ j, ξ j • A j)) (A i) ∂(standardGaussianPi n) =
      (1 / 2 : ℝ) * ∫ ξ, lap ξ ∂(standardGaussianPi n) := by
    congr 1
    apply integral_congr_ae
    apply ae_of_all
    intro ξ
    have hsum : lap ξ = ∑ i,
        secondDirectionalDerivative Φ (∑ j, ξ j • A j) (A i) := by
      dsimp [lap]
      apply Finset.sum_congr rfl
      intro i hi
      rw [nativeHeat_secondCoordinate_covarianceFactorObservable hΦ.1 0 A i ξ]
      rw [zero_add, covarianceFactorMap_apply_local]
    simpa [Real.sqrt_one] using hsum.symm
  have hcoeffBound := (hheatIdentity.symm.trans hheatLap).trans_le hupper
  have hkpos : 0 < (k + 1 : ℝ) := by positivity
  have hcoeffBound' :
      (k + 1 : ℝ) * nativeHeatCenterMoment A (k + 1) ≤
        (k + 1 : ℝ) * ((V + 2 * (k : ℝ) * L) * nativeHeatCenterMoment A k) := by
    calc
      (k + 1 : ℝ) * nativeHeatCenterMoment A (k + 1) ≤
          ((k + 1 : ℝ) * (V + 2 * (k : ℝ) * L)) *
            nativeHeatCenterMoment A k := hcoeffBound
      _ = (k + 1 : ℝ) *
            ((V + 2 * (k : ℝ) * L) * nativeHeatCenterMoment A k) := by ring
  exact (mul_le_mul_iff_of_pos_left hkpos).mp hcoeffBound'

/-- The finite Gaussian-center recurrence applies to an actual centered
Gaussian family once its normalized covariance trace and operator bounds are
proved. The family itself need not have independent coordinates. -/
theorem nativeHeatGaussianFamily_moment_step {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hX : IsCenteredGaussianFamily μ X)
    (V L : ℝ)
    (hV : (n : ℝ)⁻¹ * ∑ i, (∫ ω, (X i ω) ^ 2 ∂μ) ≤ V)
    (hL : ∀ t : Fin n → ℝ,
      (n : ℝ)⁻¹ * ∑ i, ∑ j,
          t i * t j * (∫ ω, X i ω * X j ω ∂μ) ≤
        L * ∑ i, t i ^ 2)
    (k : ℕ) (hk : 1 ≤ k) :
    (∫ ω, ((n : ℝ)⁻¹ * ∑ i, (X i ω) ^ 2) ^ (k + 1) ∂μ) ≤
      (V + 2 * (k : ℝ) * L) *
        ∫ ω, ((n : ℝ)⁻¹ * ∑ i, (X i ω) ^ 2) ^ k ∂μ := by
  let C : Fin n → Fin n → ℝ := fun i j => supMeanCovarianceFactor μ X i j
  let A : Fin n → EuclideanSpace ℝ (Fin n) := fun j =>
    WithLp.toLp 2 (fun i => C i j / Real.sqrt (n : ℝ))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hroot : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have hcoef : (Real.sqrt (n : ℝ))⁻¹ ^ 2 = (n : ℝ)⁻¹ := by
    calc
      (Real.sqrt (n : ℝ))⁻¹ ^ 2 = ((Real.sqrt (n : ℝ)) ^ 2)⁻¹ := by rw [inv_pow]
      _ = (n : ℝ)⁻¹ := by rw [Real.sq_sqrt hnR.le]
  have hrow (i : Fin n) : ∑ j, C i j ^ 2 = ∫ ω, (X i ω) ^ 2 ∂μ := by
    have hgram := supMean_covariance_factor_gram μ X hX i i
    simpa [C, pow_two] using hgram
  have hAtrace : ∑ j, ‖A j‖ ^ 2 =
      (n : ℝ)⁻¹ * ∑ i, (∫ ω, (X i ω) ^ 2 ∂μ) := by
    calc
      ∑ j, ‖A j‖ ^ 2 = ∑ j, ∑ i, (C i j / Real.sqrt (n : ℝ)) ^ 2 := by
        simp [A, EuclideanSpace.real_norm_sq_eq]
      _ = ∑ i, ∑ j, (n : ℝ)⁻¹ * C i j ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [div_pow, Real.sq_sqrt hnR.le, div_eq_mul_inv]
        ring
      _ = (n : ℝ)⁻¹ * ∑ i, (∫ ω, (X i ω) ^ 2 ∂μ) := by
        calc
          ∑ i, ∑ j, (n : ℝ)⁻¹ * C i j ^ 2 =
              ∑ i, (n : ℝ)⁻¹ * ∑ j, C i j ^ 2 := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [← Finset.mul_sum]
          _ = ∑ i, (n : ℝ)⁻¹ * ∫ ω, (X i ω) ^ 2 ∂μ := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [hrow]
          _ = (n : ℝ)⁻¹ * ∑ i, ∫ ω, (X i ω) ^ 2 ∂μ := by
                rw [← Finset.mul_sum]
  have hAop : ∀ x : EuclideanSpace ℝ (Fin n),
      ∑ j, (inner ℝ x (A j)) ^ 2 ≤ L * ‖x‖ ^ 2 := by
    intro x
    let t : Fin n → ℝ := fun i => x i
    have hinner (j : Fin n) : inner ℝ x (A j) =
        (Real.sqrt (n : ℝ))⁻¹ * ∑ i, t i * C i j := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dotProduct, Pi.star_apply, star_trivial, A]
      calc
        ∑ i, (C i j / Real.sqrt (n : ℝ)) * x i =
            ∑ i, (Real.sqrt (n : ℝ))⁻¹ * (t i * C i j) := by
              apply Finset.sum_congr rfl
              intro i hi
              simp [t, div_eq_mul_inv]
              ring
        _ = (Real.sqrt (n : ℝ))⁻¹ * ∑ i, t i * C i j := by
              rw [Finset.mul_sum]
    have hfactor := supMean_covariance_factor_quadratic μ X hX t
    calc
      ∑ j, (inner ℝ x (A j)) ^ 2 = (n : ℝ)⁻¹ *
          ∑ j, (∑ i, t i * C i j) ^ 2 := by
        simp_rw [hinner, mul_pow]
        rw [← Finset.mul_sum, hcoef]
      _ = (n : ℝ)⁻¹ *
          ∑ i, ∑ l, t i * t l * (∫ ω, X i ω * X l ω ∂μ) := by
        rw [hfactor]
      _ ≤ L * ‖x‖ ^ 2 := by
        simpa [t, EuclideanSpace.real_norm_sq_eq] using hL t
  let Y : Ω → Fin n → ℝ := fun ω i => X i ω
  let Z : (Fin n → ℝ) → Fin n → ℝ := gaussianRealizationLinearVector C
  have hId : ProbabilityTheory.IdentDistrib Y Z μ (standardGaussianPi n) := by
    refine ⟨aemeasurable_pi_iff.mpr hX.1, ?_, ?_⟩
    · apply Measurable.aemeasurable
      apply measurable_pi_iff.mpr
      intro i
      change Measurable (fun ξ : Fin n → ℝ => gaussianFiniteLinearForm (C i) ξ)
      simp only [gaussianFiniteLinearForm]
      fun_prop
    · simpa [Y, Z, C] using supMean_gaussian_finite_realization μ X hX
  have hMomentEq (r : ℕ) :
      (∫ ω, ((n : ℝ)⁻¹ * ∑ i, (X i ω) ^ 2) ^ r ∂μ) =
        nativeHeatCenterMoment A r := by
    let F : (Fin n → ℝ) → ℝ := fun z =>
      ((n : ℝ)⁻¹ * ∑ i, z i ^ 2) ^ r
    have hF : Measurable F := by fun_prop
    have hdist := hId.comp hF
    have hbase := hdist.integral_eq
    have hbase' :
        (∫ ω, F (Y ω) ∂μ) =
          ∫ ξ, F (Z ξ) ∂(standardGaussianPi n) := hbase
    have hcoord (ξ : Fin n → ℝ) (i : Fin n) :
        (∑ j, ξ j • A j) i =
          (Real.sqrt (n : ℝ))⁻¹ * Z ξ i := by
      calc
        (∑ j, ξ j • A j) i =
            ∑ j, ξ j * (C i j / Real.sqrt (n : ℝ)) := by
              simp [A, Pi.smul_apply, smul_eq_mul]
        _ = ∑ j, (Real.sqrt (n : ℝ))⁻¹ * (C i j * ξ j) := by
              apply Finset.sum_congr rfl
              intro j hj
              simp [div_eq_mul_inv]
              ring
        _ = (Real.sqrt (n : ℝ))⁻¹ * Z ξ i := by
              simp only [Z, gaussianRealizationLinearVector, gaussianFiniteLinearForm]
              rw [Finset.mul_sum]
    have hrep (ξ : Fin n → ℝ) :
        (n : ℝ)⁻¹ * ∑ i, (Z ξ i) ^ 2 =
          nativeGaussianCenterQuadratic 1 (∑ j, ξ j • A j) := by
      rw [nativeGaussianCenterQuadratic_one, EuclideanSpace.real_norm_sq_eq]
      rw [← hcoef, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoord]
      ring
    calc
      (∫ ω, ((n : ℝ)⁻¹ * ∑ i, (X i ω) ^ 2) ^ r ∂μ) =
          ∫ ξ, F (Z ξ) ∂(standardGaussianPi n) := by
            simpa [F, Y] using hbase'
      _ = nativeHeatCenterMoment A r := by
        unfold F nativeHeatCenterMoment
        apply integral_congr_ae
        filter_upwards [] with ξ
        change (((n : ℝ)⁻¹ * ∑ i, Z ξ i ^ 2) ^ r) =
          nativeGaussianCenterQuadratic 1 (∑ i, ξ i • A i) ^ r
        rw [hrep ξ]
  have hAtrBound : ∑ j, ‖A j‖ ^ 2 ≤ V := by
    rw [hAtrace]
    exact hV
  rw [hMomentEq (k + 1), hMomentEq k]
  exact nativeHeatCenterMoment_step A V L k hk hAtrBound hAop

end ASDExplicitGamma.Native
