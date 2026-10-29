module

public import ASDExplicitGamma.Inverse.PureFluxCovarianceRows
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBound
public import ASDExplicitGamma.Inverse.PureFluxGeneratorOpenBridge
public import ASDExplicitGamma.Gaussian.GaussCentering
public import ASDExplicitGamma.Gaussian.GeneratorSplit
public import ASDExplicitGamma.Inverse.RawShellSourceAlgebra
public import ASDExplicitGamma.Variational.LemmaVH2SingleFunction
public import ASDExplicitGamma.Variational.LemmaVH2Single
public import Mathlib.Analysis.MeanInequalities

/-! Source remainder rows dominate the sharper pure-flux covariance rows. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open scoped BigOperators
noncomputable section

local instance rawShellPureFluxFiniteMeasure (n : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube 2 n))) :=
  (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isFiniteMeasure_restrict_volume

/-- The first covariance coefficient in SHEAR (3.2), with source decimals represented exactly. -/
def rawTraceRemainderA (rho delta : ℝ) : ℝ :=
  1.860 * Real.sqrt (78 / 10 : ℝ) * rho +
    2.36412 * Real.sqrt (156 / 5 : ℝ) * delta +
    0.52288 * Real.sqrt (46488 / 25 : ℝ) * delta ^ 2

/-- The reciprocal covariance coefficient in SHEAR (3.2). -/
def rawTraceRemainderB (rho delta : ℝ) : ℝ :=
  1.860 * Real.sqrt (78 / 10 : ℝ) * rho +
    2.36412 * Real.sqrt (78 / 5 : ℝ) * delta +
    0.52288 * Real.sqrt (23244 / 25 : ℝ) * delta ^ 2

/-- H₀ in the exact SHEAR (4.1) source eigenvalue. -/
def rawTraceRemainderH0 : ℝ := 2.265

/-- D₀ in the exact SHEAR (4.1) source eigenvalue. -/
def rawTraceRemainderD0 : ℝ := rawTraceRemainderH0 + Real.sqrt rawTraceRemainderH0

theorem pureFlux_covariance_A_le_raw_trace_remainder_A (q i : ℕ) :
    pureFluxCovarianceA q i ≤ rawTraceRemainderA
      (pureFluxCovarianceRho q i) (pureFluxCovarianceDelta q i) := by
  have hrho := (pureFlux_covariance_rho_pos q i).le
  have hdelta := (pureFlux_covariance_delta_bounds q i).1
  have hbase : (1 : ℝ) ≤ 1.860 := by norm_num
  have hlinear : (36 / 25 : ℝ) ≤ 2.36412 := by norm_num
  have hquad : (57 / 200 : ℝ) ≤ 0.52288 := by norm_num
  have hbaseTerm : 0 ≤ (1.860 - 1) * Real.sqrt (78 / 10 : ℝ) *
      pureFluxCovarianceRho q i :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hbase) (Real.sqrt_nonneg _)) hrho
  have hlinearTerm : 0 ≤ (2.36412 - 36 / 25) * Real.sqrt (156 / 5 : ℝ) *
      pureFluxCovarianceDelta q i :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hlinear) (Real.sqrt_nonneg _)) hdelta
  have hquadTerm : 0 ≤ (0.52288 - 57 / 200) * Real.sqrt (46488 / 25 : ℝ) *
      (pureFluxCovarianceDelta q i) ^ 2 :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hquad) (Real.sqrt_nonneg _))
      (sq_nonneg _)
  unfold pureFluxCovarianceA pureFluxCovarianceAr pureFluxCovarianceBA
    pureFluxCovarianceCA rawTraceRemainderA
  rw [show ((78 / 5 : ℝ) / 2) = 78 / 10 by norm_num,
    show 2 * (78 / 5 : ℝ) = 156 / 5 by norm_num,
    show 2 * ((3432 / 5 : ℝ) + (78 / 5 : ℝ) ^ 2) = 46488 / 25 by norm_num]
  nlinarith only [hbaseTerm, hlinearTerm, hquadTerm]

theorem pureFlux_covariance_B_le_raw_trace_remainder_B (q i : ℕ) :
    pureFluxCovarianceB q i ≤ rawTraceRemainderB
      (pureFluxCovarianceRho q i) (pureFluxCovarianceDelta q i) := by
  have hrho := (pureFlux_covariance_rho_pos q i).le
  have hdelta := (pureFlux_covariance_delta_bounds q i).1
  have hbase : (1 : ℝ) ≤ 1.860 := by norm_num
  have hlinear : (36 / 25 : ℝ) ≤ 2.36412 := by norm_num
  have hquad : (57 / 200 : ℝ) ≤ 0.52288 := by norm_num
  have hbaseTerm : 0 ≤ (1.860 - 1) * Real.sqrt (78 / 10 : ℝ) *
      pureFluxCovarianceRho q i :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hbase) (Real.sqrt_nonneg _)) hrho
  have hlinearTerm : 0 ≤ (2.36412 - 36 / 25) * Real.sqrt (78 / 5 : ℝ) *
      pureFluxCovarianceDelta q i :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hlinear) (Real.sqrt_nonneg _)) hdelta
  have hquadTerm : 0 ≤ (0.52288 - 57 / 200) * Real.sqrt (23244 / 25 : ℝ) *
      (pureFluxCovarianceDelta q i) ^ 2 :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hquad) (Real.sqrt_nonneg _))
      (sq_nonneg _)
  unfold pureFluxCovarianceB pureFluxCovarianceAr pureFluxCovarianceBB
    pureFluxCovarianceCB rawTraceRemainderB
  rw [show ((78 / 5 : ℝ) / 2) = 78 / 10 by norm_num,
    show (3432 / 5 : ℝ) + (78 / 5 : ℝ) ^ 2 = 23244 / 25 by norm_num]
  nlinarith only [hbaseTerm, hlinearTerm, hquadTerm]

/-- The exact remainder eigenvalue dominates the sharper covariance
eigenvalue whenever its diagonal and cross coefficients dominate. -/
theorem pureFlux_covariance_mu_le_raw_trace_remainder_mu
    {a b A B H0 D0 : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA' : a ≤ A) (hB' : b ≤ B)
    (hH0 : 1 ≤ H0) (hD0 : 63 / 50 ≤ D0) :
    pureFluxCovarianceMu a b ≤ rawTraceRemainderMu H0 D0 A B := by
  have ha2 : a ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ ha hA' 2
  have hb2 : b ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hb hB' 2
  have ha4 : a ^ 4 ≤ A ^ 4 := pow_le_pow_left₀ ha hA' 4
  have hH02 : 1 ≤ H0 ^ 2 := by nlinarith [sq_nonneg (H0 - 1)]
  have hD02 : (63 / 50 : ℝ) ^ 2 ≤ D0 ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hD0 2
  have hA4 : 0 ≤ A ^ 4 := by positivity
  have hA2B2 : a ^ 2 * b ^ 2 ≤ A ^ 2 * B ^ 2 :=
    mul_le_mul ha2 hb2 (sq_nonneg b) (sq_nonneg A)
  have hcA2B2 : (63 / 50 : ℝ) ^ 2 * (a ^ 2 * b ^ 2) ≤
      (63 / 50 : ℝ) ^ 2 * (A ^ 2 * B ^ 2) :=
    mul_le_mul_of_nonneg_left hA2B2 (sq_nonneg (63 / 50 : ℝ))
  have hDA2B2 : (63 / 50 : ℝ) ^ 2 * (A ^ 2 * B ^ 2) ≤
      D0 ^ 2 * (A ^ 2 * B ^ 2) :=
    mul_le_mul_of_nonneg_right hD02 (mul_nonneg (sq_nonneg A) (sq_nonneg B))
  have hdiag : a ^ 2 ≤ H0 * A ^ 2 := by
    calc
      a ^ 2 ≤ A ^ 2 := ha2
      _ ≤ H0 * A ^ 2 := by nlinarith [sq_nonneg A, hH0]
  have hdisc : a ^ 4 + 4 * (63 / 50 : ℝ) ^ 2 * a ^ 2 * b ^ 2 ≤
      H0 ^ 2 * A ^ 4 + 4 * D0 ^ 2 * A ^ 2 * B ^ 2 := by
    calc
      a ^ 4 + 4 * (63 / 50 : ℝ) ^ 2 * a ^ 2 * b ^ 2 ≤
          A ^ 4 + 4 * (63 / 50 : ℝ) ^ 2 * (A ^ 2 * B ^ 2) := by
            nlinarith only [ha4, hcA2B2]
      _ ≤ H0 ^ 2 * A ^ 4 + 4 * D0 ^ 2 * A ^ 2 * B ^ 2 := by
            nlinarith only [hH02, hA4, hDA2B2]
  have hsqrt := Real.sqrt_le_sqrt hdisc
  unfold pureFluxCovarianceMu rawTraceRemainderMu
  nlinarith only [hdiag, hsqrt]

theorem pureFlux_covariance_mu_le_raw_trace_remainder_profile (q i : ℕ) :
    pureFluxCovarianceMu (pureFluxCovarianceA q i) (pureFluxCovarianceB q i) ≤
      rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
        (rawTraceRemainderA (pureFluxCovarianceRho q i)
          (pureFluxCovarianceDelta q i))
        (rawTraceRemainderB (pureFluxCovarianceRho q i)
          (pureFluxCovarianceDelta q i)) := by
  have hrows := pureFlux_covariance_rows_order q i
  have hA0 : 0 ≤ pureFluxCovarianceA q i := hrows.1.trans hrows.2
  have hB0 : 0 ≤ pureFluxCovarianceB q i := hrows.1
  have hH : 1 ≤ rawTraceRemainderH0 := by norm_num [rawTraceRemainderH0]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt rawTraceRemainderH0 :=
    Real.le_sqrt_of_sq_le (by norm_num [rawTraceRemainderH0])
  have hD : (63 / 50 : ℝ) ≤ rawTraceRemainderD0 := by
    unfold rawTraceRemainderD0
    nlinarith only [hH, hsqrt]
  exact pureFlux_covariance_mu_le_raw_trace_remainder_mu hA0 hB0
    (pureFlux_covariance_A_le_raw_trace_remainder_A q i)
    (pureFlux_covariance_B_le_raw_trace_remainder_B q i) hH hD

private theorem raw_shell_response_frame_energy_nonneg
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (P : BlockVec 2)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) :
    0 ≤ responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 n))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ P k := by
  let Q := originCube 2 n
  let U := openCubeSet Q
  let hU := isOpenBoundedConvexDomain_openCubeSet Q
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  have hset : responseFrameEnergyValueSet P ν σ k =
      (fun e : ℝ => 2 * e) '' muValueSet U P
        (responseFramePlanarCoefficientField ν σ k) :=
    responseFrameEnergyValueSet_eq_image_two_muValueSet
      (measurableSet_openCubeSet Q) P ν σ hν hσ k
  have hnon : (responseFrameEnergyValueSet P ν σ k).Nonempty := by
    rw [hset]
    exact Set.image_nonempty.mpr
      (muValueSet_nonempty U P (responseFramePlanarCoefficientField ν σ k))
  rw [responseFrameEnergyObservable_eq_sInf_energyValues hU hv ν σ hν hσ P k]
  apply le_csInf hnon
  intro e he
  exact responseFrameEnergyValueSet_nonneg (measurableSet_openCubeSet Q)
    P ν σ hν hσ k he

/-- The actual finite pure-flux load covariance is bounded by the exact
source eigenvalue. This is the remainder-source row inside (4.1),
with the coefficient comparison from (3.2); the center and mixed generator
terms are not included here. -/
theorem pureFlux_shell_finite_affine_load_generator_raw_trace_remainder
    (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    {ι : Type*} (loads : Finset ι) (P : ι → BlockVec 2) :
    let Q := originCube 2 n
    let m := pureFluxBankSourceDepth s
    let L := q3ModelLength (n+(s:ℤ))
    let B := pureFluxSourceTileHistory Q m (responseFramePlanarCoefficientField ν σ k)
    let E := fun p => responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ (P p)
    (1/2:ℝ)*(∑ p ∈ loads, modelCovarianceTrace (E p)
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k) ≤
      b^2/σ^2*rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
        (rawTraceRemainderA (pureFluxCovarianceRho 0 (s-1))
          (pureFluxCovarianceDelta 0 (s-1)))
        (rawTraceRemainderB (pureFluxCovarianceRho 0 (s-1))
          (pureFluxCovarianceDelta 0 (s-1)))*B^2*(∑ p ∈ loads, E p k) := by
  intro Q m L B E
  have hsharp := pureFlux_shell_finite_affine_load_generator
    n s hs ν σ b hν hσ k loads P
  have hmu := pureFlux_covariance_mu_le_raw_trace_remainder_profile 0 (s-1)
  have hsum : 0 ≤ ∑ p ∈ loads, E p k := by
    apply Finset.sum_nonneg
    intro p hp
    exact raw_shell_response_frame_energy_nonneg n ν σ hν hσ (P p) k
  have hscale : 0 ≤ b^2/σ^2 := by positivity
  have hcoeff : b^2/σ^2 *
      pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1))
        (pureFluxCovarianceB 0 (s-1)) ≤
      b^2/σ^2 * rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
        (rawTraceRemainderA (pureFluxCovarianceRho 0 (s-1))
          (pureFluxCovarianceDelta 0 (s-1)))
        (rawTraceRemainderB (pureFluxCovarianceRho 0 (s-1))
          (pureFluxCovarianceDelta 0 (s-1))) :=
    mul_le_mul_of_nonneg_left hmu hscale
  calc
    (1/2:ℝ)*(∑ p ∈ loads, modelCovarianceTrace (E p)
        (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k) ≤
        b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1))
          (pureFluxCovarianceB 0 (s-1))*B^2*(∑ p ∈ loads, E p k) := hsharp
    _ = (b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1))
          (pureFluxCovarianceB 0 (s-1)))*(B^2*(∑ p ∈ loads, E p k)) := by ring
    _ ≤ (b^2/σ^2*rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
          (rawTraceRemainderA (pureFluxCovarianceRho 0 (s-1))
            (pureFluxCovarianceDelta 0 (s-1)))
          (rawTraceRemainderB (pureFluxCovarianceRho 0 (s-1))
            (pureFluxCovarianceDelta 0 (s-1))))*(B^2*(∑ p ∈ loads, E p k)) :=
      mul_le_mul_of_nonneg_right hcoeff (mul_nonneg (sq_nonneg B) hsum)
    _ = _ := by ring

/-- The same finite affine-load remainder generator row with the exact 340
covariance eigenvalue, before the historical SHEAR (3.2) outward rounding. -/
theorem pureFlux_shell_finite_affine_load_generator_tight
    (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n)))
    {ι : Type*} (loads : Finset ι) (P : ι → BlockVec 2) :
    let Q := originCube 2 n
    let m := pureFluxBankSourceDepth s
    let L := q3ModelLength (n+(s:ℤ))
    let B := pureFluxSourceTileHistory Q m (responseFramePlanarCoefficientField ν σ k)
    let E := fun p => responseFrameEnergyObservable (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ (P p)
    (1/2:ℝ)*(∑ p ∈ loads, modelCovarianceTrace (E p)
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k) ≤
      b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1))
        (pureFluxCovarianceB 0 (s-1))*B^2*(∑ p ∈ loads, E p k) := by
  exact pureFlux_shell_finite_affine_load_generator n s hs ν σ b hν hσ k loads P

/-- The actual centered q3 remainder covariance of the OLD trace is bounded
by the exact remainder row. The four physical loads are assembled on
the same restricted coefficient and sum to the full trace plus four. -/
theorem raw_trace_model_q3_remainder_covariance_row_tight
    (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let L := q3ModelLength (n+(s:ℤ))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let R := fun j => centeringMap center (H j)
    let k := pureFluxOpenResponseRestriction n x
    let B := pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ k)
    (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable n ν σ) R x ≤
      b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1))
        (pureFluxCovarianceB 0 (s-1))*B^2*
        (modelTraceObservable n ν σ x + 4) := by
  classical
  intro Q L center H R k B
  let P : Fin 2 × Bool → BlockVec 2 := fun p =>
    orthonormalFrameLoad p.1 (lemmaVLoadSign p.2)
  let E : (Fin 2 × Bool) → ResponseCoefficient (openCubeSet Q) → ℝ :=
    lemmaVLoadEnergy n ν σ hν hσ
  have hH0 : Summable (fun j => ‖H j‖ ^ 2) := by
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet (originCube 2 n)), ℝ) inferInstance
      (mainCubeH3InnerProductSpace n b L).toNormedSpace inferInstance inferInstance
      (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L)
      (mainCubeH3Value n b L)
  have hH : Summable (fun j => ‖R j‖ ^ 2) := by
    exact summable_sq_bounded_image H hH0 (centeringMap center)
  have hcenter (j : ℕ) : R j = pureFluxCoefficientCentering center (H j) := by
    ext y
    simp [R, centeringMap, pureFluxCoefficientCentering, smul_eq_mul]
  have hrestrict (j : ℕ) : pureFluxOpenResponseRestriction n (R j) =
      pureFluxMainCubeQ3CenteredResponseCoefficient n b L j := by
    rw [hcenter]
    exact (pureFluxMainCubeQ3CenteredResponseCoefficient_eq_restriction n b L j).symm
  have hload (p : Fin 2 × Bool) :
      modelCovarianceTrace (E p) (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ (P p) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    exact responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ (P p)
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k
  have htrace := modelTrace_covarianceTrace_eq_open_four_load_hessians
    n ν σ hν hσ R hH x
  have hload00 : modelCovarianceTrace (E (0, true))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 0 1) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (0, true)
  have hload01 : modelCovarianceTrace (E (0, false))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 0 (-1)) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (0, false)
  have hload10 : modelCovarianceTrace (E (1, true))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 1 1) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (1, true)
  have hload11 : modelCovarianceTrace (E (1, false))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 1 (-1)) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (1, false)
  have hcov : modelCovarianceTrace (modelTraceObservable n ν σ) R x =
      ∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)),
        modelCovarianceTrace (E p) (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k := by
    have htrace' := htrace
    simp_rw [hrestrict] at htrace'
    rw [← hload00, ← hload01, ← hload10, ← hload11] at htrace'
    rw [htrace']
    simp [E, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  have henergy :
      (∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)), E p k) =
        modelTraceObservable n ν σ x + 4 := by
    have hsum := lemmaVTrace_eq_load_sum n ν σ hν hσ k
    have htraceOpen := modelTraceObservable_eq_lemmaVTrace_openRestriction
      n ν σ hν hσ x
    have hsum' :
        (∑ p : Fin 2 × Bool, lemmaVLoadEnergy n ν σ hν hσ p k) =
          lemmaVTrace n ν σ k + 4 := by linarith [hsum]
    simpa [E] using
      hsum'.trans (congrArg (fun z : ℝ => z + 4) htraceOpen.symm)
  have hbound := pureFlux_shell_finite_affine_load_generator_tight
    n s hs ν σ b hν hσ k Finset.univ P
  dsimp only at hbound
  have hbound' :
      (1/2:ℝ)*(∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)),
        modelCovarianceTrace (E p) (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k) ≤
        b^2/σ^2*pureFluxCovarianceMu (pureFluxCovarianceA 0 (s-1))
        (pureFluxCovarianceB 0 (s-1))*B^2*
          (∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)), E p k) := by
    simpa [E, P, lemmaVLoadEnergy, lemmaVLoadSign] using hbound
  rw [← hcov, henergy] at hbound'
  simpa [Q, L, center, H, R, k, B] using hbound'


theorem raw_trace_model_q3_remainder_covariance_row
    (n : ℤ) (s : ℕ) (hs : 1 ≤ s) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let L := q3ModelLength (n+(s:ℤ))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let R := fun j => centeringMap center (H j)
    let k := pureFluxOpenResponseRestriction n x
    let B := pureFluxSourceTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ k)
    (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable n ν σ) R x ≤
      b^2/σ^2*rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
        (rawTraceRemainderA (pureFluxCovarianceRho 0 (s-1))
          (pureFluxCovarianceDelta 0 (s-1)))
        (rawTraceRemainderB (pureFluxCovarianceRho 0 (s-1))
          (pureFluxCovarianceDelta 0 (s-1)))*B^2*
        (modelTraceObservable n ν σ x + 4) := by
  classical
  intro Q L center H R k B
  let P : Fin 2 × Bool → BlockVec 2 := fun p =>
    orthonormalFrameLoad p.1 (lemmaVLoadSign p.2)
  let E : (Fin 2 × Bool) → ResponseCoefficient (openCubeSet Q) → ℝ :=
    lemmaVLoadEnergy n ν σ hν hσ
  have hH0 : Summable (fun j => ‖H j‖ ^ 2) := by
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet (originCube 2 n)), ℝ) inferInstance
      (mainCubeH3InnerProductSpace n b L).toNormedSpace inferInstance inferInstance
      (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L)
      (mainCubeH3Value n b L)
  have hH : Summable (fun j => ‖R j‖ ^ 2) := by
    exact summable_sq_bounded_image H hH0 (centeringMap center)
  have hcenter (j : ℕ) : R j = pureFluxCoefficientCentering center (H j) := by
    ext y
    simp [R, centeringMap, pureFluxCoefficientCentering, smul_eq_mul]
  have hrestrict (j : ℕ) : pureFluxOpenResponseRestriction n (R j) =
      pureFluxMainCubeQ3CenteredResponseCoefficient n b L j := by
    rw [hcenter]
    exact (pureFluxMainCubeQ3CenteredResponseCoefficient_eq_restriction n b L j).symm
  have hload (p : Fin 2 × Bool) :
      modelCovarianceTrace (E p) (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ (P p) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    exact responseFrameEnergyObservable_covarianceTrace_eq_hessianDiagonal_sum
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ (P p)
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k
  have htrace := modelTrace_covarianceTrace_eq_open_four_load_hessians
    n ν σ hν hσ R hH x
  have hload00 : modelCovarianceTrace (E (0, true))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 0 1) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (0, true)
  have hload01 : modelCovarianceTrace (E (0, false))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 0 (-1)) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (0, false)
  have hload10 : modelCovarianceTrace (E (1, true))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 1 1) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (1, true)
  have hload11 : modelCovarianceTrace (E (1, false))
      (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k =
        ∑' j, pureFluxResponseHessianDiagonal (measurableSet_openCubeSet Q)
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ
          (orthonormalFrameLoad 1 (-1)) k
          (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j) := by
    simpa [E, P, lemmaVLoadSign] using hload (1, false)
  have hcov : modelCovarianceTrace (modelTraceObservable n ν σ) R x =
      ∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)),
        modelCovarianceTrace (E p) (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k := by
    have htrace' := htrace
    simp_rw [hrestrict] at htrace'
    rw [← hload00, ← hload01, ← hload10, ← hload11] at htrace'
    rw [htrace']
    simp [E, Fintype.sum_prod_type, Fin.sum_univ_two]
    ring
  have henergy :
      (∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)), E p k) =
        modelTraceObservable n ν σ x + 4 := by
    have hsum := lemmaVTrace_eq_load_sum n ν σ hν hσ k
    have htraceOpen := modelTraceObservable_eq_lemmaVTrace_openRestriction
      n ν σ hν hσ x
    have hsum' :
        (∑ p : Fin 2 × Bool, lemmaVLoadEnergy n ν σ hν hσ p k) =
          lemmaVTrace n ν σ k + 4 := by linarith [hsum]
    simpa [E] using
      hsum'.trans (congrArg (fun z : ℝ => z + 4) htraceOpen.symm)
  have hbound := pureFlux_shell_finite_affine_load_generator_raw_trace_remainder
    n s hs ν σ b hν hσ k Finset.univ P
  dsimp only at hbound
  have hbound' :
      (1/2:ℝ)*(∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)),
        modelCovarianceTrace (E p) (pureFluxMainCubeQ3CenteredResponseCoefficient n b L) k) ≤
        b^2/σ^2*rawTraceRemainderMu rawTraceRemainderH0 rawTraceRemainderD0
          (rawTraceRemainderA (pureFluxCovarianceRho 0 (s-1))
            (pureFluxCovarianceDelta 0 (s-1)))
          (rawTraceRemainderB (pureFluxCovarianceRho 0 (s-1))
            (pureFluxCovarianceDelta 0 (s-1)))*B^2*
          (∑ p ∈ (Finset.univ : Finset (Fin 2 × Bool)), E p k) := by
    simpa [E, P, lemmaVLoadEnergy, lemmaVLoadSign] using hbound
  rw [← hcov, henergy] at hbound'
  simpa [Q, L, center, H, R, k, B] using hbound'

/-- The actual q3 shell has point variance `b²` at the parent center. This
is the scalar center covariance consumed by the constant-shear row. -/
theorem pureFluxMainCubeQ3_parentCenter_variance
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    (∑' j, (pureFluxMainCubeQ3Directions n b L j
      (pureFluxParentCenter n)) ^ 2) = b ^ 2 := by
  have hcenter : cubeCenter (originCube 2 n) = 0 := by
    ext i
    simp [cubeCenter, originCube]
  have hvalue (j : ℕ) :
      pureFluxMainCubeQ3Directions n b L j (pureFluxParentCenter n) =
        q3Convolution b L h3Zero (gaussEnumerated whiteBasis j) 0 := by
    rw [pureFluxMainCubeQ3Directions, mainCubeH3Value_direction]
    simp [mainQ3GlobalDirection, pureFluxParentCenter, hcenter]
  have hc0 : q3Cov 0 = 1 := by
    rw [q3Cov]
    simpa only [add_zero, ← sq] using Model.q3Kernel_sq_integral
  have hcov := main_q3_direction_covariance whiteBasis b L
    h3Zero h3Zero 0 0
  have hsum := hcov.tsum_eq
  rw [q3Section_covariance] at hsum
  have hsum' :
      (∑' i : whiteBasisIndex,
        (q3Convolution b L h3Zero (whiteBasis i) 0) ^ 2) = b ^ 2 := by
    simpa [hc0, pow_two] using hsum
  calc
    (∑' j, (pureFluxMainCubeQ3Directions n b L j
        (pureFluxParentCenter n)) ^ 2) =
        ∑' j, (q3Convolution b L h3Zero
          (gaussEnumerated whiteBasis j) 0) ^ 2 := by
            apply tsum_congr
            intro j
            rw [hvalue]
    _ = ∑' i : whiteBasisIndex,
        (q3Convolution b L h3Zero (whiteBasis i) 0) ^ 2 :=
          enumerated_tsum_apply whiteBasis
            (fun u => (q3Convolution b L h3Zero u 0) ^ 2)
            (by simp [q3Convolution])
    _ = b ^ 2 := hsum'

private theorem raw_trace_secondDirectionalDerivative_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (x v : E) :
    secondDirectionalDerivative f x v =
      deriv (deriv (fun t : ℝ => f (x + t • v))) 0 := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ v
  let G : E → ℝ := fun y => fderiv ℝ f y v
  let φ : ℝ → ℝ := fun t => f (x + t • v)
  have hfirst (t : ℝ) : deriv φ t = G (x + L t) := by
    have houter := (hf.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
      (x + L t)).hasFDerivAt
    have hinner : HasFDerivAt (fun z : ℝ => x + L z) L t :=
      L.hasFDerivAt.const_add x
    have hcomp := houter.comp t hinner
    have hderiv := hcomp.hasDerivAt.deriv
    simpa [φ, G, L, Function.comp_def] using hderiv
  have hEval := hf.contDiff_fderiv_apply (m := 1)
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
  have hpair : ContDiff ℝ 1 (fun y : E => (y, v)) :=
    contDiff_id.prodMk contDiff_const
  have hG : ContDiff ℝ 1 G := by
    simpa [G, Function.comp_def] using hEval.comp hpair
  have hcomp := (hG.differentiable_one (x + L 0)).hasFDerivAt.comp (0 : ℝ)
    (L.hasFDerivAt.const_add x)
  have hsecondLine : deriv (fun t : ℝ => G (x + L t)) 0 =
      fderiv ℝ G x v := by
    have hderiv := hcomp.hasDerivAt.deriv
    simpa [G, L, Function.comp_def] using hderiv
  have hfirstFun : deriv φ = fun t : ℝ => G (x + L t) :=
    funext hfirst
  calc
    secondDirectionalDerivative f x v = fderiv ℝ G x v := by
      rfl
    _ = deriv (deriv φ) 0 := by
      rw [hfirstFun]
      exact hsecondLine.symm
    _ = deriv (deriv (fun t : ℝ => f (x + t • v))) 0 := rfl

private theorem raw_trace_secondDirectionalDerivative_of_quadratic_line
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (x v : E) (a b c : ℝ)
    (hline : ∀ t : ℝ, f (x + t • v) = a + b * t + c * t ^ 2) :
    secondDirectionalDerivative f x v = 2 * c := by
  rw [raw_trace_secondDirectionalDerivative_line hf x v]
  let p : ℝ → ℝ := fun t => a + b * t + c * t ^ 2
  have hfun : (fun t : ℝ => f (x + t • v)) = p := by
    funext t
    exact hline t
  rw [hfun]
  have hpoly (t : ℝ) : HasDerivAt p (b + 2 * c * t) t := by
    have hlin : HasDerivAt (fun s : ℝ => b * s) b t := by
      simpa [mul_comm] using (hasDerivAt_id t).const_mul b
    have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using (hasDerivAt_pow 2 t)
    have hquad : HasDerivAt (fun s : ℝ => c * s ^ 2) (2 * c * t) t := by
      convert (hasDerivAt_const t c).mul hpow using 1
      all_goals ring_nf
    have hsum := (hasDerivAt_const t a).add (hlin.add hquad)
    have hpFun : p = (fun _ : ℝ => a) +
        ((fun s : ℝ => b * s) + fun s : ℝ => c * s ^ 2) := by
      funext s
      simp [p]
      ring
    rw [← hpFun] at hsum
    simpa [zero_add] using hsum
  have hderivFun : deriv p = fun t : ℝ => b + 2 * c * t :=
    funext fun t => (hpoly t).deriv
  have hsecond : HasDerivAt (fun t : ℝ => b + 2 * c * t) (2 * c) 0 := by
    convert (hasDerivAt_const (0 : ℝ) b).add
      ((hasDerivAt_const (0 : ℝ) (2 * c)).mul (hasDerivAt_id (0 : ℝ))) using 1
    · funext t
      simp
    · ring
  rw [hderivFun]
  exact hsecond.deriv

private theorem raw_trace_model_constant_shear_line
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let K := closure (cubeSet Q)
    let e : C(K, ℝ) := ContinuousMap.const K 1
    let k : ResponseCoefficient (cubeSet Q) :=
      ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ x
    let A := coarseBlockMatrix (cubeSet Q) (responsePlanarCoefficientField ν k)
    ∀ t : ℝ, modelTraceObservable n ν σ (x + t • e) =
      modelTraceObservable n ν σ x +
        2 * (Variational.shearTraceLinear A / σ) * t +
          (Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2) * t ^ 2 := by
  classical
  intro Q K e k A t
  let cMap : C(K, ℝ) →L[ℝ] ResponseCoefficient (cubeSet Q) :=
    ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ
  have he : cMap e = BoundedContinuousFunction.const K 1 := by
    ext y
    change (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ e) y = 1
    simp [e]
  have hmap : cMap (x + t • e) =
      k + t • BoundedContinuousFunction.const K 1 := by
    calc
      cMap (x + t • e) = cMap x + cMap (t • e) := map_add cMap x _
      _ = k + t • cMap e := by rw [map_smul]; rfl
      _ = k + t • BoundedContinuousFunction.const K 1 := by rw [he]
  have hAE : responsePlanarCoefficientField ν (cMap (x + t • e)) =ᵐ[
      volume.restrict (cubeSet Q)]
      (fun y => responsePlanarCoefficient ν
        (responseCoefficientExtension k y + t)) := by
    rw [hmap]
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_cubeSet Q)] with y hy
    unfold responsePlanarCoefficientField
    have hext : responseCoefficientExtension
        (k + t • BoundedContinuousFunction.const K 1) y =
        responseCoefficientExtension k y + t := by
      rw [responseCoefficientExtension_add_on k _ hy,
        responseCoefficientExtension_smul_on t _ hy,
        responseCoefficientExtension_eq (BoundedContinuousFunction.const K 1) hy,
        BoundedContinuousFunction.const_apply']
      ring
    rw [hext]
  have hshift : modelTraceObservable n ν σ (x + t • e) =
      traceDefect (cubeSet Q)
        (fun y => responsePlanarCoefficient ν (responseCoefficientExtension k y + t)) σ := by
    unfold modelTraceObservable
    change traceDefect (cubeSet Q)
      (responsePlanarCoefficientField ν (cMap (x + t • e))) σ = _
    unfold traceDefect
    rw [coarseBlockMatrix_congr_of_ae_eq hAE]
  have hsource := response_traceDefect_constantSkew_physical Q ν σ hν hσ k t
  have hbase : modelTraceObservable n ν σ x =
      traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ := rfl
  calc
    modelTraceObservable n ν σ (x + t • e) =
        traceDefect (cubeSet Q)
          (fun y => responsePlanarCoefficient ν (responseCoefficientExtension k y + t)) σ :=
      hshift
    _ = traceDefect (cubeSet Q) (responsePlanarCoefficientField ν k) σ +
          2 * (t / σ) * Variational.shearTraceLinear A +
          t ^ 2 * (Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2) := hsource
    _ = modelTraceObservable n ν σ x +
          2 * (Variational.shearTraceLinear A / σ) * t +
          (Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2) * t ^ 2 := by
      rw [← hbase]
      ring

/-- The first derivative of the actual OLD trace along constant shear is the
source linear coefficient in the true frame. -/
theorem raw_trace_model_constant_shear_first_derivative
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let K := closure (cubeSet (originCube 2 n))
    let k : ResponseCoefficient (cubeSet (originCube 2 n)) :=
      ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ x
    let A := coarseBlockMatrix (cubeSet (originCube 2 n))
      (responsePlanarCoefficientField ν k)
    σ * fderiv ℝ (modelTraceObservable n ν σ) x (1 : C(K, ℝ)) =
      2 * Variational.shearTraceLinear A := by
  classical
  intro K k A
  let e : C(K, ℝ) := ContinuousMap.const K 1
  let φ : ℝ → ℝ := fun t => modelTraceObservable n ν σ (x + t • e)
  let p : ℝ → ℝ := fun t => modelTraceObservable n ν σ x +
    (2 * (Variational.shearTraceLinear A / σ) * t +
      (Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2) * t ^ 2)
  have he : e = (1 : C(K, ℝ)) := by
    ext y
    simp [e]
  have hline := raw_trace_model_constant_shear_line n ν σ hν hσ x
  have hfun : φ = p := by
    funext t
    dsimp [φ, p]
    rw [hline t]
    ring
  let L : ℝ →L[ℝ] C(K, ℝ) := ContinuousLinearMap.toSpanSingleton ℝ e
  have hcomp := (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives
      n ν σ hν hσ).1.differentiable
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0) (x + L 0)
  have hchain := hcomp.hasFDerivAt.comp 0 (L.hasFDerivAt.const_add x)
  have hfirst : deriv φ 0 = fderiv ℝ (modelTraceObservable n ν σ) x e := by
    have hderiv := hchain.hasDerivAt.deriv
    simpa [φ, L, Function.comp_def] using hderiv
  have hlinear : HasDerivAt
      (fun t : ℝ => 2 * (Variational.shearTraceLinear A / σ) * t)
      (2 * (Variational.shearTraceLinear A / σ)) 0 := by
    simpa [mul_comm] using
      (hasDerivAt_id (0 : ℝ)).const_mul
        (2 * (Variational.shearTraceLinear A / σ))
  have hquadratic : HasDerivAt
      (fun t : ℝ => (Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2) * t ^ 2)
      0 0 := by
    convert (hasDerivAt_const (0 : ℝ)
      (Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2)).mul
        (hasDerivAt_pow 2 (0 : ℝ)) using 1
    all_goals ring_nf
  have hpderiv : deriv p 0 = 2 * (Variational.shearTraceLinear A / σ) := by
    have hpoly : HasDerivAt p (2 * (Variational.shearTraceLinear A / σ)) 0 := by
      simpa [p] using (hlinear.add hquadratic).const_add
        (modelTraceObservable n ν σ x)
    exact hpoly.deriv
  have hfirst' := hfirst
  rw [hfun] at hfirst'
  have hD : fderiv ℝ (modelTraceObservable n ν σ) x (1 : C(K, ℝ)) =
      2 * (Variational.shearTraceLinear A / σ) := by
    rw [← he]
    exact hfirst'.symm.trans hpderiv
  calc
    σ * fderiv ℝ (modelTraceObservable n ν σ) x (1 : C(K, ℝ)) =
        σ * (2 * (Variational.shearTraceLinear A / σ)) := by rw [hD]
    _ = 2 * Variational.shearTraceLinear A := by field_simp [hσ.ne']

/-- The exact center part of the actual q3 generator is its scalar center
variance times the OLD trace Hessian in the constant direction. -/
theorem raw_trace_model_q3_center_generator_eq
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let K := closure (cubeSet (originCube 2 n))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let C : C(K, ℝ) →L[ℝ] (Fin 1 → ℝ) :=
      ContinuousLinearMap.pi fun _ => ContinuousMap.evalCLM ℝ center
    let I : (Fin 1 → ℝ) →L[ℝ] C(K, ℝ) :=
      (ContinuousLinearMap.proj (0 : Fin 1)).smulRight (1 : C(K, ℝ))
    centerGenerator H C I
        (fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x) =
      (b ^ 2 / 2) * secondDirectionalDerivative (modelTraceObservable n ν σ) x
        (1 : C(K, ℝ)) := by
  intro K center H C I
  let B := fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x
  let e : C(K, ℝ) := ContinuousMap.const K 1
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet (originCube 2 n)), ℝ) inferInstance
      (mainCubeH3InnerProductSpace n b L).toNormedSpace inferInstance inferInstance
      (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L)
      (mainCubeH3Value n b L)
  have hdir (j : ℕ) : I (C (H j)) = (H j center) • e := by
    ext y
    simp [I, C, e, ContinuousMap.evalCLM_apply]
  have hterm (j : ℕ) : B (I (C (H j))) (I (C (H j))) =
      (H j center) ^ 2 * B e e := by
    rw [hdir]
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hvariance := pureFluxMainCubeQ3_parentCenter_variance n b L
  have hHessian : B e e =
      secondDirectionalDerivative (modelTraceObservable n ν σ) x e := by
    dsimp [B, secondDirectionalDerivative]
    exact (second_fderiv_eq
      (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n ν σ hν hσ).1
      x e e).symm
  have he : e = (1 : C(K, ℝ)) := by
    ext y
    simp [e]
  calc
    centerGenerator H C I B =
        (1 / 2 : ℝ) * ∑' j, B (I (C (H j))) (I (C (H j))) :=
          (center_generator_eq hH C I B).symm
    _ = (1 / 2 : ℝ) * ((∑' j, (H j center) ^ 2) * B e e) := by
          simp_rw [hterm]
          rw [tsum_mul_right]
    _ = (b ^ 2 / 2) * secondDirectionalDerivative
        (modelTraceObservable n ν σ) x (1 : C(K, ℝ)) := by
          rw [hvariance]
          rw [hHessian]
          rw [he]
          ring_nf

/-- The parent-center q3 generator is the exact constant-shear trace row
`b² tr(D)`, with the actual OLD response matrix. -/
theorem raw_trace_model_q3_center_shear_row
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let K := closure (cubeSet (originCube 2 n))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let C : C(K, ℝ) →L[ℝ] (Fin 1 → ℝ) :=
      ContinuousLinearMap.pi fun _ => ContinuousMap.evalCLM ℝ center
    let I : (Fin 1 → ℝ) →L[ℝ] C(K, ℝ) :=
      (ContinuousLinearMap.proj (0 : Fin 1)).smulRight (1 : C(K, ℝ))
    let k : ResponseCoefficient (cubeSet (originCube 2 n)) :=
      ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ x
    let A := coarseBlockMatrix (cubeSet (originCube 2 n))
      (responsePlanarCoefficientField ν k)
    centerGenerator H C I
        (fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x) =
      b ^ 2 * (Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2) := by
  intro K center H C I k A
  let e : C(K, ℝ) := ContinuousMap.const K 1
  have he : e = (1 : C(K, ℝ)) := by
    ext y
    simp [e]
  have hline := raw_trace_model_constant_shear_line n ν σ hν hσ x
  have hline' : ∀ t : ℝ, modelTraceObservable n ν σ (x + t • e) =
      modelTraceObservable n ν σ x +
        2 * (Variational.shearTraceLinear A / σ) * t +
          (Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2) * t ^ 2 := by
    simpa [e, k, A] using hline
  have hhess : secondDirectionalDerivative (modelTraceObservable n ν σ) x e =
      2 * (Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2) := by
    exact raw_trace_secondDirectionalDerivative_of_quadratic_line
      (modelTraceObservable_hasPolynomiallyBoundedC2Derivatives n ν σ hν hσ).1
      x e (modelTraceObservable n ν σ x)
      (2 * (Variational.shearTraceLinear A / σ))
      (Matrix.trace (frameMatrix σ A).lowerRight / σ ^ 2) hline'
  rw [raw_trace_model_q3_center_generator_eq n ν σ b hν hσ L x]
  rw [← he, hhess]
  ring

/-- The center/remainder cross covariance of the actual q3 directions is the
deterministic covariance defect, with no decorrelation assumption. -/
theorem pureFluxMainCubeQ3_parentCenter_remainder_covariance
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : closure (cubeSet (originCube 2 n))) :
    (∑' j, pureFluxMainCubeQ3Directions n b L j (pureFluxParentCenter n) *
      (pureFluxMainCubeQ3Directions n b L j x -
        pureFluxMainCubeQ3Directions n b L j (pureFluxParentCenter n))) =
      b ^ 2 * (q3Cov ((0 - x.1 0) / L.1) *
        q3Cov ((0 - x.1 1) / L.1) - 1) := by
  have hcenter : cubeCenter (originCube 2 n) = 0 := by
    ext i
    simp [cubeCenter, originCube]
  have hvalue0 (j : ℕ) :
      pureFluxMainCubeQ3Directions n b L j (pureFluxParentCenter n) =
        q3Convolution b L h3Zero (gaussEnumerated whiteBasis j) 0 := by
    rw [pureFluxMainCubeQ3Directions, mainCubeH3Value_direction]
    simp [mainQ3GlobalDirection, pureFluxParentCenter, hcenter]
  have hvalueX (j : ℕ) :
      pureFluxMainCubeQ3Directions n b L j x =
        q3Convolution b L h3Zero (gaussEnumerated whiteBasis j) x.1 := by
    rw [pureFluxMainCubeQ3Directions, mainCubeH3Value_direction]
    rfl
  have hc0 : q3Cov 0 = 1 := by
    rw [q3Cov]
    simpa only [add_zero, ← sq] using Model.q3Kernel_sq_integral
  have hxy := main_q3_direction_covariance whiteBasis b L
    h3Zero h3Zero 0 x.1
  have h00 := main_q3_direction_covariance whiteBasis b L
    h3Zero h3Zero 0 0
  have hlim :
      inner ℝ (q3Section b L h3Zero 0) (q3Section b L h3Zero x.1) -
        inner ℝ (q3Section b L h3Zero 0) (q3Section b L h3Zero 0) =
      b ^ 2 * (q3Cov ((0 - x.1 0) / L.1) *
        q3Cov ((0 - x.1 1) / L.1) - 1) := by
    rw [q3Section_covariance, q3Section_covariance]
    simp [hc0]
    ring
  have hmixBasis : HasSum
      (fun i : whiteBasisIndex =>
        q3Convolution b L h3Zero (whiteBasis i) 0 *
          (q3Convolution b L h3Zero (whiteBasis i) x.1 -
            q3Convolution b L h3Zero (whiteBasis i) 0))
      (b ^ 2 * (q3Cov ((0 - x.1 0) / L.1) *
        q3Cov ((0 - x.1 1) / L.1) - 1)) := by
    have h := hxy.sub h00
    convert h using 1
    · funext i
      ring
    · exact hlim.symm
  calc
    _ = ∑' j, q3Convolution b L h3Zero
        (gaussEnumerated whiteBasis j) 0 *
          (q3Convolution b L h3Zero (gaussEnumerated whiteBasis j) x.1 -
            q3Convolution b L h3Zero (gaussEnumerated whiteBasis j) 0) := by
          apply tsum_congr
          intro j
          rw [hvalue0, hvalueX]
    _ = ∑' i : whiteBasisIndex,
        q3Convolution b L h3Zero (whiteBasis i) 0 *
          (q3Convolution b L h3Zero (whiteBasis i) x.1 -
            q3Convolution b L h3Zero (whiteBasis i) 0) :=
          enumerated_tsum_apply whiteBasis
            (fun u => q3Convolution b L h3Zero u 0 *
              (q3Convolution b L h3Zero u x.1 -
                q3Convolution b L h3Zero u 0)) (by simp [q3Convolution])
    _ = b ^ 2 * (q3Cov ((0 - x.1 0) / L.1) *
        q3Cov ((0 - x.1 1) / L.1) - 1) := hmixBasis.tsum_eq

private theorem raw_center_remainder_vector_summable
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (H : ℕ → C(K, ℝ)) (center : K)
    (hH : Summable (fun j => ‖H j‖ ^ 2)) :
    Summable (fun j => (H j center) • centeringMap center (H j)) := by
  let eval : C(K, ℝ) →L[ℝ] ℝ := ContinuousMap.evalCLM ℝ center
  let R : C(K, ℝ) →L[ℝ] C(K, ℝ) := centeringMap center
  have hcoeff : Summable (fun j => ‖eval (H j)‖ ^ 2) :=
    summable_sq_norm_map hH eval
  have hrem : Summable (fun j => ‖R (H j)‖ ^ 2) :=
    summable_sq_norm_map hH R
  have hcoeffR : Summable (fun j => ‖eval (H j)‖ ^ (2 : ℝ)) := by
    exact hcoeff.congr (fun j => (Real.rpow_natCast _ _).symm)
  have hremR : Summable (fun j => ‖R (H j)‖ ^ (2 : ℝ)) := by
    exact hrem.congr (fun j => (Real.rpow_natCast _ _).symm)
  have h22 : Real.HolderConjugate (2 : ℝ) 2 := by
    exact (Real.holderConjugate_iff_eq_conjExponent
      (by norm_num : (1 : ℝ) < 2)).2 (by norm_num [Real.conjExponent])
  have hprod : Summable (fun j => ‖eval (H j)‖ * ‖R (H j)‖) := by
    exact Real.summable_mul_of_Lp_Lq_of_nonneg
      (f := fun j => ‖eval (H j)‖) (g := fun j => ‖R (H j)‖)
      h22 (fun j => norm_nonneg (eval (H j)))
      (fun j => norm_nonneg (R (H j))) hcoeffR hremR
  have hterms : Summable (fun j => (H j center) • R (H j)) := by
    apply Summable.of_norm_bounded hprod
    intro j
    simp [eval, ContinuousMap.evalCLM_apply, norm_smul]
  simpa [eval, R, ContinuousMap.evalCLM_apply, norm_smul] using hterms

private theorem raw_q3_center_remainder_vector_summable
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    Summable (fun j => (pureFluxMainCubeQ3Directions n b L j
      (pureFluxParentCenter n)) • centeringMap (pureFluxParentCenter n)
        (pureFluxMainCubeQ3Directions n b L j)) := by
  let H3 := MainCubeH3 n b L
  have hH : Summable (fun j => ‖pureFluxMainCubeQ3Directions n b L j‖ ^ 2) := by
    exact @summable_sq_bounded_image ℕ H3
      C(closure (cubeSet (originCube 2 n)), ℝ) inferInstance
      (mainCubeH3InnerProductSpace n b L).toNormedSpace inferInstance inferInstance
      (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L)
      (mainCubeH3Value n b L)
  exact raw_center_remainder_vector_summable
    (pureFluxMainCubeQ3Directions n b L) (pureFluxParentCenter n) hH

private theorem raw_q3_center_remainder_vector_tsum
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    let K := closure (cubeSet (originCube 2 n))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    (∑' j, (H j center) • centeringMap center (H j)) =
      b ^ 2 • (⟨fun y : K =>
        q3CovarianceDefect L.1 center.1 y.1,
        (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp
          continuous_subtype_val⟩ : C(K, ℝ)) := by
  intro K center H
  have hterms : Summable (fun j => (H j center) • centeringMap center (H j)) := by
    simpa [H, center] using raw_q3_center_remainder_vector_summable n b L
  let R : C(K, ℝ) →L[ℝ] C(K, ℝ) := centeringMap center
  let defect : C(K, ℝ) :=
    ⟨fun y => q3CovarianceDefect L.1 center.1 y.1,
      (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp
        continuous_subtype_val⟩
  have hcenter : cubeCenter (originCube 2 n) = 0 := by
    ext i
    simp [cubeCenter, originCube]
  have hpoint (y : K) :
      q3Cov ((0 - y.1 0) / L.1) * q3Cov ((0 - y.1 1) / L.1) - 1 =
        defect y := by
    have harg0 : (0 - y.1 0) / L.1 = -((y.1 0 - 0) / L.1) := by ring
    have harg1 : (0 - y.1 1) / L.1 = -((y.1 1 - 0) / L.1) := by ring
    change q3Cov ((0 - y.1 0) / L.1) * q3Cov ((0 - y.1 1) / L.1) - 1 =
      q3CovarianceDefect L.1 center.1 y.1
    rw [show center.1 = cubeCenter (originCube 2 n) by rfl, hcenter]
    unfold q3CovarianceDefect ASDExplicitGamma.Model.q3ProductCovariance
    rw [harg0, harg1, ASDExplicitGamma.Model.q3Cov_even,
      ASDExplicitGamma.Model.q3Cov_even]
    rfl
  apply ContinuousMap.ext
  intro y
  have heval := (ContinuousMap.evalCLM ℝ y).map_tsum hterms
  have hcov := pureFluxMainCubeQ3_parentCenter_remainder_covariance n b L y
  calc
    (∑' j, (H j center) • R (H j)) y =
        ∑' j, ((H j center) • R (H j)) y := by
          simpa only [ContinuousMap.evalCLM_apply] using heval
    _ = ∑' j, (H j center) * (H j y - H j center) := by
      apply tsum_congr
      intro j
      simp [R, centeringMap_apply, smul_eq_mul]
    _ = b ^ 2 * defect y := by rw [hcov, hpoint]
    _ = (b ^ 2 • defect) y := by simp

/- The exact mixed row below is the actual covariance-defect direction; its
formal p=20 estimate is the next source-bound step. -/
theorem raw_trace_model_q3_mixed_generator_eq_covariance_defect
    (n : ℤ) (ν σ b : ℝ) (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let K := closure (cubeSet (originCube 2 n))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let C : C(K, ℝ) →L[ℝ] (Fin 1 → ℝ) :=
      ContinuousLinearMap.pi fun _ => ContinuousMap.evalCLM ℝ center
    let I : (Fin 1 → ℝ) →L[ℝ] C(K, ℝ) :=
      (ContinuousLinearMap.proj (0 : Fin 1)).smulRight (1 : C(K, ℝ))
    let R := centeringMap center
    let B := fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x
    mixedGenerator H C I R B =
      B (1 : C(K, ℝ)) (b ^ 2 • (⟨fun y : K =>
        q3CovarianceDefect L.1 center.1 y.1,
        (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp
          continuous_subtype_val⟩ : C(K, ℝ))) := by
  intro K center H C I R B
  let e : C(K, ℝ) := ContinuousMap.const K 1
  have he : e = (1 : C(K, ℝ)) := by
    ext y
    simp [e]
  have hterms : Summable (fun j => (H j center) • centeringMap center (H j)) := by
    simpa [H, center, R] using raw_q3_center_remainder_vector_summable n b L
  let defect : C(K, ℝ) :=
    ⟨fun y => q3CovarianceDefect L.1 center.1 y.1,
      (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp
        continuous_subtype_val⟩
  have hvector : (∑' j, (H j center) • R (H j)) = b ^ 2 • defect := by
    simpa [defect, R, H] using raw_q3_center_remainder_vector_tsum n b L
  have hmixedShape : mixedGenerator H C I R B =
      ∑' j, (H j center) * B e (R (H j)) := by
    unfold mixedGenerator
    apply tsum_congr
    intro j
    simp [C, I, e, ContinuousMap.evalCLM_apply]
  calc
    mixedGenerator H C I R B =
        ∑' j, (H j center) * B e (R (H j)) := hmixedShape
    _ = B e (∑' j, (H j center) • R (H j)) := by
      let ℓ : C(K, ℝ) →L[ℝ] ℝ := B e
      calc
        _ = ∑' j, ℓ ((H j center) • R (H j)) := by
          apply tsum_congr
          intro j
          simp [ℓ, map_smul]
        _ = ℓ (∑' j, (H j center) • R (H j)) := (ℓ.map_tsum hterms).symm
    _ = B (1 : C(K, ℝ)) (b ^ 2 • defect) := by
      rw [hvector, he]

/-- The deterministic mixed coefficient from SHEAR (3.3), with the source
decimals represented exactly. -/
def rawTraceRemainderKappaF (rho delta : ℝ) : ℝ :=
  1.860 * ((78 / 5 : ℝ) / 4) * rho ^ 2 +
    2.36412 * ((78 / 5 : ℝ) / Real.sqrt 2) * rho * delta +
    0.52288 * Real.sqrt 2 * (78 / 5 : ℝ) * delta ^ 2

/-- The canonical q3 covariance-defect row coefficient is bounded by the
outward mixed coefficient in SHEAR (3.3). -/
theorem lemmaVH2kn_le_rawTraceRemainderKappaF
    {rho delta : ℝ} (hrho : 0 ≤ rho) (hdelta : 0 ≤ delta) :
    ASDExplicitGamma.Variational.lemmaVH2kn rho delta ≤
      rawTraceRemainderKappaF rho delta := by
  have h0 : (1 : ℝ) ≤ 1.860 := by norm_num
  have h1 : (36 / 25 : ℝ) ≤ 2.36412 := by norm_num
  have h2 : (57 / 200 : ℝ) ≤ 0.52288 := by norm_num
  have hbase : 0 ≤ ((78 / 5 : ℝ) / 4) * rho ^ 2 := by positivity
  have hlinear : 0 ≤ ((78 / 5 : ℝ) / Real.sqrt 2) * rho * delta := by positivity
  have hquad : 0 ≤ Real.sqrt 2 * (78 / 5 : ℝ) * delta ^ 2 := by positivity
  have hb := mul_le_mul_of_nonneg_right h0 hbase
  have hl := mul_le_mul_of_nonneg_right h1 hlinear
  have hq := mul_le_mul_of_nonneg_right h2 hquad
  simp only [ASDExplicitGamma.Variational.lemmaVH2kn,
    ASDExplicitGamma.Variational.lemmaVH2R1,
    ASDExplicitGamma.Variational.lemmaVH2C1,
    ASDExplicitGamma.Variational.lemmaVH2C2, rawTraceRemainderKappaF]
  nlinarith only [hb, hl, hq]

/-- The actual q3 covariance-defect source row with the sharp finite-p mixed
coefficient from SHEAR (3.3). The product-kernel defect remains the actual
center/remainder covariance direction. -/
theorem raw_trace_q3_covariance_defect_H2_row_tight
    (Q : TriadicCube 2) (j : ℕ) {L : ℝ} (hL : 0 < L)
    (p : Vec 2) (u : H10Function (openCubeSet Q))
    (t : Finset ℕ) (c : ℕ → ℝ) :
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    let η := q3CovarianceDefectFamily Q L
    (∀ R ∈ descendantsAtDepth Q j, ∀ b, Summable (fun n => (Real.sqrt 3) ^ (n + 1) *
      energy R (cubeIncrement R (n + 1)
        (fun x => lemmaVRowCombination I (fun l => (η l).value) φ t c x b)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q j
      (lemmaVRowCombination I (fun l => (η l).value) φ t c)) ≤
      lemmaVH2kn (cubeScaleFactor Q / L) (diagMeshRadius Q j / L) *
        Real.sqrt (∑ l ∈ t, c l ^ 2) *
          Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad) := by
  dsimp only
  exact lemmaV_H2_single Q j hL p u t c

/-- Actual q3 covariance-defect source row in the mixed SHEAR coefficient.
The centered product-kernel direction is the one used by the model
generator identity above; its complete localized row is bounded with the
source `κ_f` coefficient, without any decorrelation premise. -/
theorem raw_trace_q3_covariance_defect_H2_row
    (Q : TriadicCube 2) (j : ℕ) {L : ℝ} (hL : 0 < L)
    (p : Vec 2) (u : H10Function (openCubeSet Q))
    (t : Finset ℕ) (c : ℕ → ℝ) :
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    let η := q3CovarianceDefectFamily Q L
    (∀ R ∈ descendantsAtDepth Q j, ∀ b, Summable (fun n => (Real.sqrt 3) ^ (n + 1) *
      energy R (cubeIncrement R (n + 1)
        (fun x => lemmaVRowCombination I (fun l => (η l).value) φ t c x b)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q j
      (lemmaVRowCombination I (fun l => (η l).value) φ t c)) ≤
      rawTraceRemainderKappaF (cubeScaleFactor Q / L) (diagMeshRadius Q j / L) *
        Real.sqrt (∑ l ∈ t, c l ^ 2) *
          Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad) := by
  dsimp only
  have hsource := lemmaV_H2_single Q j hL p u t c
  have hρ : 0 ≤ cubeScaleFactor Q / L :=
    div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le hL.le
  have hδ : 0 ≤ diagMeshRadius Q j / L :=
    div_nonneg (diagMeshRadius_pos Q j).le hL.le
  have hcoeff := lemmaVH2kn_le_rawTraceRemainderKappaF hρ hδ
  have hweight₀ : 0 ≤ Real.sqrt (∑ l ∈ t, c l ^ 2) := Real.sqrt_nonneg _
  have hweight₁ : 0 ≤ Real.sqrt (lemmaVTiledWeakEnergy Q j
      (lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u).grad) :=
    Real.sqrt_nonneg _
  have hstep₀ := mul_le_mul_of_nonneg_right hcoeff hweight₀
  have hstep₁ := mul_le_mul_of_nonneg_right hstep₀ hweight₁
  refine ⟨hsource.1, hsource.2.trans ?_⟩
  exact hstep₁

/-- Exact actual-law Gaussian generator split for the fresh q3 shell at the
parent center. The mixed covariance is retained, and the final directions are
the same centered directions used in the preceding μ_R row. -/
theorem raw_trace_model_q3_generator_split
    (n : ℤ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let K := closure (cubeSet (originCube 2 n))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let C : C(K, ℝ) →L[ℝ] (Fin 1 → ℝ) :=
      ContinuousLinearMap.pi fun _ => ContinuousMap.evalCLM ℝ center
    let I : (Fin 1 → ℝ) →L[ℝ] C(K, ℝ) :=
      (ContinuousLinearMap.proj (0 : Fin 1)).smulRight (1 : C(K, ℝ))
    let R := centeringMap center
    (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable n ν σ) H x =
      centerGenerator H C I (fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x) +
      mixedGenerator H C I R (fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x) +
      (1/2:ℝ)*∑' j, fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x
        (R (H j)) (R (H j)) := by
  intro K center H C I R
  let P : C(K, ℝ) →L[ℝ] C(K, ℝ) := ContinuousLinearMap.id ℝ _
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet (originCube 2 n)), ℝ) inferInstance
      (mainCubeH3InnerProductSpace n b L).toNormedSpace inferInstance inferInstance
      (mainCubeQ3Directions n b L) (mainCubeQ3Directions_summable n b L)
      (mainCubeH3Value n b L)
  have hΦ := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives
    n ν σ hν hσ
  have hcomp : I.comp C =
      (ContinuousMap.evalCLM ℝ center).smulRight (1 : C(K, ℝ)) := by
    ext f y
    simp [I, C, ContinuousMap.evalCLM_apply]
  have hR : P - I.comp C = centeringMap center := by
    rw [hcomp]
    rfl
  have hsplit := response_generator_split hH P C I hΦ.1 x
  rw [hR] at hsplit
  change (1/2:ℝ)*modelCovarianceTrace (modelTraceObservable n ν σ) H x =
      centerGenerator H C I (fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x) +
      mixedGenerator H C I R (fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x) +
      (1/2:ℝ)*∑' j, fderiv ℝ (fderiv ℝ (modelTraceObservable n ν σ)) x
        (R (H j)) (R (H j)) at hsplit
  exact hsplit

end
end ASDExplicitGamma.Inverse
