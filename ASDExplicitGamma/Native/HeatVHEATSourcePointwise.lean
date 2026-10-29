/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Native.HeatVHEATRefinedThetaPointwise
public import ASDExplicitGamma.Native.HeatVHEATSourceFinalAssembly
public import ASDExplicitGamma.Native.HeatVHEATBracketSourceCarrier
public import ASDExplicitGamma.Native.HeatVHEATSourceBracket

/-! The source-normalized pointwise generator on the unscaled carrier. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Gaussian Algsuperdiff.Section3 Numerics.Native
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal NNReal
noncomputable section

local instance nativeHeatVHEATSourcePointwiseIndexNeZero :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance nativeHeatVHEATSourcePointwiseChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn
      (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

local instance nativeHeatVHEATSourcePointwiseChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace
      (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

/-- The actual cancelled generator whose auxiliary center covariance is
`(1 + θ) * (1 - t)` times the source center covariance. -/
noncomputable def nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ) (r : ℕ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) : ℝ := by
  let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
    fun i => nativeHeatQ3RefinedCarrierChild m i
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
  let hvol : ∀ i, 0 < (volume (U i)).toReal :=
    fun i => volume_cubeSet_toReal_pos (Q i)
  let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun i => closure (U i)
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1
  let I := childConstantMap V
  let S := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let W := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
  let P := (nativeHeatQ3RefinedCarrierOldMap m).comp S
  let L := (nativeHeatQ3RefinedCarrierSourceCenterMap m).comp S
  let c := fun i => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian
    M h hM m θ t i z.2
  let y := nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 + I c
  exact cancelledGenerator W P L I (fun f => μ f ^ r) θ y

/-- The exact cancellation identifies this integrand with the physical
power generator minus the fully normalized source-center generator. -/
theorem nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGenerator_eq_powerDifference
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ)
    (r : ℕ) (hr : 2 ≤ r)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal :=
      fun i => volume_cubeSet_toReal_pos (Q i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
      fun i => closure (U i)
    let σ : ℝ := Annealed.sigmaBar M (m + 1)
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M (m + 1)).1
    let I := childConstantMap V
    let S := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
    let W := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
    let P := (nativeHeatQ3RefinedCarrierOldMap m).comp S
    let C₀ := (childCenterMap (nativeHeatQ3RefinedCarrierCenter m)).comp S
    let y := nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 + I
      (fun i => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian
        M h hM m θ t i z.2)
    nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
        M h hM m θ t r z =
      modelPowerHeatGenerator μ (fun j => P (W j)) (r : ℝ) y -
        (1 + θ) * modelPowerHeatGenerator μ
          (fun j => I (C₀ (W j))) (r : ℝ) y := by
  classical
  unfold nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
  let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
    fun i => nativeHeatQ3RefinedCarrierChild m i
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
  let hvol : ∀ i, 0 < (volume (U i)).toReal :=
    fun i => volume_cubeSet_toReal_pos (Q i)
  let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun i => closure (U i)
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M (m + 1)).1
  let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
  let I := childConstantMap V
  let S := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let W := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
  let P := (nativeHeatQ3RefinedCarrierOldMap m).comp S
  let C₀ := (childCenterMap (nativeHeatQ3RefinedCarrierCenter m)).comp S
  let c := fun i => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian
    M h hM m θ t i z.2
  let y := nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 + I c
  simpa only [nativeHeatQ3RefinedCarrierSourceCenterMap] using
    (nativeHeatQ3RefinedCarrierSourceCenterCancelledPowerGenerator_eq
      M h hM m σ hσ θ
      (nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1) c r hr)

private theorem nativeHeatVHEATSourceGradientBracket_eq
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}
    (H : ℕ → E) (hH : Summable (fun j => ‖H j‖ ^ 2))
    (P R : E →L[ℝ] X) (C : E →L[ℝ] (Fin n → ℝ))
    (I : (Fin n → ℝ) →L[ℝ] X) (D : X →L[ℝ] ℝ)
    (coeff θ : ℝ) (hP : P = R + I.comp C) :
    (coeff / 2) *
        (tsum (fun j : ℕ => (D (P (H j))) ^ 2) -
          (1 + θ) * tsum (fun j : ℕ => (D (I (C (H j)))) ^ 2)) =
      -θ * centerGenerator H C I (coeff • D.smulRight D) +
        mixedGenerator H C I R (coeff • D.smulRight D) +
        (1 / 2 : ℝ) * ∑' j, (coeff • D.smulRight D) (R (H j)) (R (H j)) := by
  classical
  let B := coeff • D.smulRight D
  let a : ℕ → ℝ := fun j => D (I (C (H j)))
  let b : ℕ → ℝ := fun j => D (R (H j))
  have ha : Summable (fun j => (a j) ^ 2) := by
    have hs := summable_sq_norm_map hH (D.comp (I.comp C))
    simpa only [a, ContinuousLinearMap.comp_apply,
      Real.norm_eq_abs, sq_abs] using hs
  have hb : Summable (fun j => (b j) ^ 2) := by
    have hs := summable_sq_norm_map hH (D.comp R)
    simpa only [b, ContinuousLinearMap.comp_apply,
      Real.norm_eq_abs, sq_abs] using hs
  let mulB : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ ℝ)
  have hab : Summable (fun j => a j * b j) := by
    have hs := summable_bilinear_images hH mulB
      (D.comp (I.comp C)) (D.comp R)
    simpa only [mulB, a, b, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      smul_apply, smul_eq_mul] using hs
  have hPdirection (j : ℕ) : D (P (H j)) = a j + b j := by
    calc
      D (P (H j)) = D ((R + I.comp C) (H j)) := by rw [hP]
      _ = D (R (H j)) + D (I (C (H j))) := by
        change D (R (H j) + I (C (H j))) = _
        exact map_add D _ _
      _ = a j + b j := by dsimp [a, b]; ring
  have hgradP : tsum (fun j : ℕ => (D (P (H j))) ^ 2) =
      tsum (fun j : ℕ => (a j + b j) ^ 2) := by
    apply tsum_congr
    intro j
    rw [hPdirection j]
  have hgradC : tsum (fun j : ℕ => (D (I (C (H j)))) ^ 2) =
      tsum (fun j : ℕ => (a j) ^ 2) := by
    apply tsum_congr
    intro j
    rfl
  have hquad : tsum (fun j : ℕ => (a j + b j) ^ 2) -
      (1 + θ) * tsum (fun j : ℕ => (a j) ^ 2) =
      -θ * tsum (fun j : ℕ => (a j) ^ 2) +
        2 * tsum (fun j : ℕ => a j * b j) +
        tsum (fun j : ℕ => (b j) ^ 2) := by
    have hpoint (j : ℕ) : (a j + b j) ^ 2 =
        (a j) ^ 2 + 2 * (a j * b j) + (b j) ^ 2 := by ring
    calc
      _ = tsum (fun j : ℕ =>
          (a j) ^ 2 + 2 * (a j * b j) + (b j) ^ 2) -
          (1 + θ) * tsum (fun j : ℕ => (a j) ^ 2) := by
            congr 1
            exact tsum_congr hpoint
      _ = _ := by
        rw [(ha.add (hab.mul_left 2)).tsum_add hb,
          ha.tsum_add (hab.mul_left 2), tsum_mul_left]
        ring
  have hcenterPoint (j : ℕ) : B (I (C (H j))) (I (C (H j))) =
      coeff * (a j) ^ 2 := by
    simp only [B, ContinuousLinearMap.smulRight_apply, smul_apply,
      smul_eq_mul, a]
    ring
  have hcenterSum : (∑' j, B (I (C (H j))) (I (C (H j)))) =
      coeff * (∑' j, (a j) ^ 2) := by
    calc
      _ = ∑' j, coeff * (a j) ^ 2 := tsum_congr hcenterPoint
      _ = _ := tsum_mul_left
  have hcenterGen : centerGenerator H C I B =
      (coeff / 2) * (∑' j, (a j) ^ 2) := by
    have h := center_generator_eq hH C I B
    rw [hcenterSum] at h
    nlinarith [h]
  have hmixedPoint (j : ℕ) :
      B (I (C (H j))) (R (H j)) = coeff * (a j * b j) := by
    simp only [B, ContinuousLinearMap.smulRight_apply, smul_apply,
      smul_eq_mul, a, b]
  have hmixedGen : mixedGenerator H C I R B =
      coeff * (∑' j, a j * b j) := by
    calc
      _ = ∑' j, B (I (C (H j))) (R (H j)) :=
        (mixed_generator_eq H C I R B).symm
      _ = ∑' j, coeff * (a j * b j) := tsum_congr hmixedPoint
      _ = _ := tsum_mul_left
  have hresidualPoint (j : ℕ) :
      B (R (H j)) (R (H j)) = coeff * (b j) ^ 2 := by
    simp only [B, ContinuousLinearMap.smulRight_apply, smul_apply,
      smul_eq_mul, b]
    ring
  have hresidualGen : (1 / 2 : ℝ) *
      ∑' j, B (R (H j)) (R (H j)) =
      (coeff / 2) * (∑' j, (b j) ^ 2) := by
    calc
      _ = (1 / 2 : ℝ) * ∑' j, coeff * (b j) ^ 2 := by
        rw [tsum_congr hresidualPoint]
      _ = _ := by rw [tsum_mul_left]; ring
  calc
    _ = coeff * (-(θ / 2) * ∑' j, (a j) ^ 2 +
        ∑' j, a j * b j + (1 / 2 : ℝ) * ∑' j, (b j) ^ 2) := by
      rw [hgradP, hgradC, hquad]
      ring
    _ = -θ * centerGenerator H C I B +
        mixedGenerator H C I R B +
        (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) := by
      rw [hcenterGen, hmixedGen, hresidualGen]
      ring

/-- At degree one, the source-normalized center subtraction leaves exactly the
off-diagonal covariance row. The extra `θ` center covariance has the favorable
sign by convexity of the mean trace. -/
theorem nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGenerator_le_drift_one
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ t : ℝ) (hθ : 0 < θ)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
    nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
        M h hM m θ t 1 z ≤
      heatVHEATDriftRefinedPhysicalDrift M h m t 1
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t) z := by
  classical
  let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
    fun i => nativeHeatQ3RefinedCarrierChild m i
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
  let hvol : ∀ i, 0 < (volume (U i)).toReal :=
    fun i => volume_cubeSet_toReal_pos (Q i)
  let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M (m + 1)).1
  let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
  let I := childConstantMap V
  let C₀ := childCenterMap (nativeHeatQ3RefinedCarrierCenter m)
  let S := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let W := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
  let H : ℕ → C(nativeHeatQ3RefinedCarrierDomain m, ℝ) := fun j => S (W j)
  let P₀ := nativeHeatQ3RefinedCarrierOldMap m
  let P := P₀.comp S
  let L := (nativeHeatQ3RefinedCarrierSourceCenterMap m).comp S
  let c := fun i => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian
    M h hM m θ t i z.2
  let fields := nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 + I c
  let g := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t
  have hW : Summable (fun j => ‖W j‖ ^ 2) :=
    nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m
  have hμpoly : HasPolynomiallyBoundedC2Derivatives μ := by
    simpa [μ, U, hU, hvol, σ] using
      childMeanTrace_polynomial U hU hvol M.nu σ M.nu_pos hσ
  have hcancel : cancelledGenerator W P L I (fun f => μ f) θ fields =
      (1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => P (W j)) fields -
        ((1 + θ) / 2) * modelCovarianceTrace μ (fun j => I (L (W j))) fields := by
    calc
      _ = backwardGenerator (fun f => μ f) (fun j => P (W j))
          (fun j => I (L (W j))) θ fields :=
            (congrFun (generator_cancellation hW P L I hμpoly.1 θ) fields).symm
      _ = _ := rfl
  have hgen :
      nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
          M h hM m θ t 1 z =
        (1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => P (W j)) fields -
          ((1 + θ) / 2) * modelCovarianceTrace μ (fun j => I (L (W j))) fields := by
    change cancelledGenerator W P L I (fun f => μ f ^ (1 : ℕ)) θ fields = _
    simpa only [pow_one] using hcancel
  have hcov := nativeHeatQ3RefinedCarrierMeanCovariance_minus_center_le_offDiagonal
    M h hM m σ hσ fields
  have hcov' :
      (1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => P₀ (H j)) fields -
        (1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => I (C₀ (H j))) fields ≤
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
            M h m i d σ (fields i)) := by
    simpa only [Q, U, hU, hvol, V, σ, hσ, μ, I, C₀, H, P₀,
      nativeHeatQ3RefinedCarrierSourceCenterMap,
      ContinuousLinearMap.comp_apply] using hcov
  have hcenter (j : ℕ) :
      0 ≤ secondDirectionalDerivative μ fields (I (C₀ (H j))) := by
    have hraw := nativeHeat_childMeanTrace_secondDirectional_nonneg
      Q M.nu σ M.nu_pos hσ fields (fun _ => 0) (C₀ (H j))
    have hIzero : I (fun _ : nativeHeatQ3RefinedCarrierIndex => (0 : ℝ)) = 0 :=
      map_zero I
    change 0 ≤ secondDirectionalDerivative μ
      (fields + I (fun _ => 0)) (I (C₀ (H j))) at hraw
    rw [hIzero, add_zero] at hraw
    exact hraw
  have hcenterCov : 0 ≤ (1 / 2 : ℝ) *
      modelCovarianceTrace μ (fun j => I (C₀ (H j))) fields := by
    rw [modelCovarianceTrace]
    exact mul_nonneg (by norm_num) (tsum_nonneg hcenter)
  have hcenterExcess : -θ * ((1 / 2 : ℝ) *
      modelCovarianceTrace μ (fun j => I (C₀ (H j))) fields) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ.le) hcenterCov
  have hfields' : ∀ i,
      fields i = heatVHEATDriftRefinedChildField m t g z i := by
    intro i
    change nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 i +
        childConstantMap V c i = _
    ext x
    simp [nativeHeatQ3RefinedCarrierPhysicalBaseChildren,
      heatVHEATDriftRefinedChildField, childConstantMap, V, c, g]
  have hprofile :
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
            M h m i d σ (fields i)) =
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
            M h m i d σ
              (heatVHEATDriftRefinedChildField m t g z i)) := by
    have hsum :
        (∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
            M h m i d σ (fields i)) =
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
            M h m i d σ
              (heatVHEATDriftRefinedChildField m t g z i) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro d hd
      rw [hfields' i]
    exact congrArg (fun q : ℝ =>
      (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ * q) hsum
  have hcard : (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ) =
      ((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ) := by
    have hnat : Fintype.card nativeHeatQ3RefinedCarrierIndex = 3 ^ 10 * 3 ^ 10 := by
      calc
        Fintype.card nativeHeatQ3RefinedCarrierIndex = 9 ^ 10 :=
          nativeHeatQ3RefinedCarrierIndex_card
        _ = (3 * 3) ^ 10 := by norm_num
        _ = 3 ^ 10 * 3 ^ 10 := mul_pow 3 3 10
    exact_mod_cast hnat
  have hrow : nativeHeatQ3RefinedCarrierOffDiagonalGeneratorRow M h m t 1 g z =
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
            M h m i d σ
              (heatVHEATDriftRefinedChildField m t g z i)) := by
    have hformRaw := nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow_eq_generatorForm
      M h m t 1 g z
    have hform : (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
            M h m i d (Annealed.sigmaBar M (m + 1))
              (heatVHEATDriftRefinedChildField m t g z i)) =
        nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow M h m t 1 g z := by
      simpa only [Nat.cast_one, Nat.sub_self, pow_zero, one_mul] using hformRaw
    have hfirst := nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow_eq
      M h m t 1 g z
    have hgenerator := nativeHeatQ3RefinedCarrierOffDiagonalGeneratorRow_eq
      M h m t 1 (by norm_num) g z
    have hrowFirst :
        nativeHeatQ3RefinedCarrierOffDiagonalGeneratorRow M h m t 1 g z =
          nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow M h m t 1 g z :=
      hgenerator.trans hfirst.symm
    have hrowLiteral := hrowFirst.trans hform.symm
    rw [hcard]
    simpa only [σ] using hrowLiteral
  change _ ≤ heatVHEATDriftRefinedPhysicalDrift M h m t 1 g z
  rw [hgen]
  calc
    _ = ((1 / 2 : ℝ) * modelCovarianceTrace μ
          (fun j => P₀ (H j)) fields -
        (1 / 2 : ℝ) * modelCovarianceTrace μ
          (fun j => I (C₀ (H j))) fields) +
        (-θ * ((1 / 2 : ℝ) * modelCovarianceTrace μ
          (fun j => I (C₀ (H j))) fields)) := by
          simp only [P, P₀, H, L, C₀, S, W,
            nativeHeatQ3RefinedCarrierSourceCenterMap,
            ContinuousLinearMap.comp_apply]
          ring
    _ ≤ ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
          ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
            nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
              M h m i d σ (fields i)) + 0 :=
            add_le_add hcov' hcenterExcess
    _ = nativeHeatQ3RefinedCarrierOffDiagonalGeneratorRow M h m t 1 g z := by
          rw [hprofile, ← hrow]
          simp
    _ = heatVHEATDriftRefinedPhysicalDrift M h m t 1 g z :=
      nativeHeatQ3RefinedCarrierOffDiagonalGeneratorRow_eq
        M h m t 1 (by norm_num) g z

/-- The source-normalized pointwise row. The inflated-center cancellation
removes the θ-center clock exactly; the remaining residual square is bounded
by the actual nine-shell coefficient-4 profile row. -/
theorem nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGenerator_le_driftAndBracket
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (θ : ℝ) (hθ : 0 < θ)
    (_hγ : 0 < M.gamma)
    (_hstate : nativeInductionState M h (m + 1))
    (t : ℝ) (r : ℕ) (hr : 2 ≤ r)
    (z : Cutoff.CutoffSample 2 × (ℕ → ℝ)) :
    let g := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t
    let fields := nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 +
      childConstantMap
        (fun i : nativeHeatQ3RefinedCarrierIndex =>
          closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) (fun i => g i z.2)
    let A := heatVHEATDriftRefinedPhysicalAverage M m t g z
    let coeffAvg := (r : ℝ) * ((r : ℝ) - 1) * A ^ (r - 2)
    nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
        M h hM m θ t r z ≤
      heatVHEATDriftRefinedPhysicalDrift M h m t r g z +
        (coeffAvg / 2) * ((1 + θ⁻¹) *
          nativeHeatQ3RefinedCarrierSourceRowsForFields M h m fields) := by
  classical
  let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
    fun i => nativeHeatQ3RefinedCarrierChild m i
  let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
  let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
  let hvol : ∀ i, 0 < (volume (U i)).toReal :=
    fun i => volume_cubeSet_toReal_pos (Q i)
  let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
    fun i => closure (U i)
  let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
    nativeHeatQ3RefinedCarrierChild_closure_subset m
  let σ : ℝ := Annealed.sigmaBar M (m + 1)
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M (m + 1)).1
  let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
  let I := childConstantMap V
  let C := nativeHeatQ3RefinedCarrierSourceCenterMap m
  let S := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
  let W := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
  let H : ℕ → C(nativeHeatQ3RefinedCarrierDomain m, ℝ) := fun j => S (W j)
  let P₀ := nativeHeatQ3RefinedCarrierOldMap m
  let P := P₀.comp S
  let L := (nativeHeatQ3RefinedCarrierSourceCenterMap m).comp S
  let R₀ := childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
  let R := P₀ - I.comp C
  let c := fun i => nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian
    M h hM m θ t i z.2
  let fields := nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 + I c
  let g := nativeHeatQ3RefinedCarrierSourceAuxCenterGaussian M h hM m θ t
  let coeff := (r : ℝ) * ((r : ℝ) - 1) * (μ fields) ^ (r - 2)
  let coeffAvg := (r : ℝ) * ((r : ℝ) - 1) *
    (heatVHEATDriftRefinedPhysicalAverage M m t g z) ^ (r - 2)
  let D := fderiv ℝ μ fields
  let B : (∀ i, C(V i, ℝ)) →L[ℝ] (∀ i, C(V i, ℝ)) →L[ℝ] ℝ :=
    coeff • D.smulRight D
  let sourceRows := nativeHeatQ3RefinedCarrierSourceRowsForFields M h m fields
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    exact summable_sq_norm_map
      (nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m)
      (nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m)
  have hfields' : ∀ i,
      fields i = heatVHEATDriftRefinedChildField m t g z i := by
    intro i
    change nativeHeatQ3RefinedCarrierPhysicalBaseChildren m t z.1 i +
        childConstantMap V c i = _
    ext x
    simp [nativeHeatQ3RefinedCarrierPhysicalBaseChildren,
      heatVHEATDriftRefinedChildField, childConstantMap, V, c, g]
  have hmean : μ fields =
      heatVHEATDriftRefinedPhysicalAverage M m t g z := by
    rw [nativeHeatQ3RefinedCarrierPhysicalAverage_eq_childMeanTrace]
    apply congrArg (fun x : ∀ i, C(V i, ℝ) =>
      childMeanTrace U hU hvol M.nu σ M.nu_pos hσ x)
    funext i
    exact hfields' i
  have hmeanActual : μ fields =
      childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
        (fun i => heatVHEATDriftRefinedChildField m t g z i) := by
    rw [hmean, nativeHeatQ3RefinedCarrierPhysicalAverage_eq_childMeanTrace]
  have hcoeff : coeff = coeffAvg := by
    dsimp [coeff, coeffAvg]
    rw [hmean]
  have hgenPower :
      nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
          M h hM m θ t r z =
        modelPowerHeatGenerator μ (fun j => P₀ (H j)) (r : ℝ) fields -
          (1 + θ) * modelPowerHeatGenerator μ
            (fun j => I (C (H j))) (r : ℝ) fields := by
    simpa only [Q, U, hU, hvol, V, σ, hσ, μ, I, C, S, W, H, P, P₀,
      C, L, c, fields, nativeHeatQ3RefinedCarrierSourceCenterMap,
      ContinuousLinearMap.comp_apply] using
      (nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGenerator_eq_powerDifference
        M h hM m θ t r hr z)
  have hpowCast : (μ fields) ^ ((r : ℝ) - 2) = (μ fields) ^ (r - 2) := by
    have hcast : ((r - 2 : ℕ) : ℝ) = (r : ℝ) - 2 := by
      exact Nat.cast_sub (by exact_mod_cast hr : 2 ≤ r)
    rw [← hcast]
    exact Real.rpow_natCast _ _
  have hpowerCoeff : ((r : ℝ) * ((r : ℝ) - 1) / 2) *
      (μ fields) ^ ((r : ℝ) - 2) = coeff / 2 := by
    dsimp only [coeff]
    rw [hpowCast]
    ring
  have hgenEq :
      nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
          M h hM m θ t r z =
        (r : ℝ) * (μ fields) ^ ((r : ℝ) - 1) *
          ((1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => P₀ (H j)) fields -
            ((1 + θ) / 2) *
              modelCovarianceTrace μ (fun j => I (C (H j))) fields) +
        (coeff / 2) *
          (modelGradientSquareTrace μ (fun j => P₀ (H j)) fields -
            (1 + θ) * modelGradientSquareTrace μ (fun j => I (C (H j))) fields) := by
    rw [hgenPower]
    unfold modelPowerHeatGenerator
    rw [hpowerCoeff]
    ring
  have hcov := nativeHeatQ3RefinedCarrierMeanCovariance_minus_center_le_offDiagonal
    M h hM m σ hσ fields
  have hcov' :
      (1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => P₀ (H j)) fields -
        (1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => I (C (H j))) fields ≤
      ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
        ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
          nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
            M h m i d σ (fields i)) := by
    simpa only [Q, U, hU, hvol, V, hV, σ, μ, I, C, H, P₀,
      nativeHeatQ3RefinedCarrierSourceCenterMap] using hcov
  have hμnonneg : 0 ≤ μ fields :=
    nativeHeat_childMeanTrace_nonneg Q M.nu σ M.nu_pos hσ fields
  have hfactor : 0 ≤ (r : ℝ) * (μ fields) ^ ((r : ℝ) - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hμnonneg _)
  have hcenter := nativeHeatQ3RefinedCarrierSourceCenterDrift_signOnSourceCarrier
    M m θ hθ H fields r hr
  have hcenter' :
      -θ * ((r : ℝ) * (μ fields) ^ ((r : ℝ) - 1) *
        ((1 / 2 : ℝ) * modelCovarianceTrace μ
          (fun j => I (C (H j))) fields)) ≤ 0 := by
    simpa only [Q, U, hU, hvol, V, σ, hσ, μ, I, C, H] using hcenter.2
  have hfieldsProfile :
      (∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
        nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
          M h m i d σ (fields i)) =
      ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
        nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
          M h m i d σ (heatVHEATDriftRefinedChildField m t g z i) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro d hd
    rw [hfields' i]
  have hnorm : (Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ =
      (((3 ^ 10 * 3 ^ 10 : ℕ) : ℝ)⁻¹) := by
    norm_num [nativeHeatQ3RefinedCarrierIndex]
  have hFirst :
      (r : ℝ) * (μ fields) ^ ((r : ℝ) - 1) *
          ((1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => P₀ (H j)) fields -
            ((1 + θ) / 2) *
              modelCovarianceTrace μ (fun j => I (C (H j))) fields) ≤
        heatVHEATDriftRefinedPhysicalDrift M h m t r g z := by
    have hscaled := mul_le_mul_of_nonneg_left hcov' hfactor
    have hform := nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow_eq_actualGeneratorForm
      M h m t r (by omega) g z
    have hrow := nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow_eq
      M h m t r g z
    calc
      _ = (r : ℝ) * (μ fields) ^ ((r : ℝ) - 1) *
          ((1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => P₀ (H j)) fields -
            (1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => I (C (H j))) fields) +
          -θ * ((r : ℝ) * (μ fields) ^ ((r : ℝ) - 1) *
            ((1 / 2 : ℝ) * modelCovarianceTrace μ
              (fun j => I (C (H j))) fields)) := by ring
      _ ≤ (r : ℝ) * (μ fields) ^ ((r : ℝ) - 1) *
          ((Fintype.card nativeHeatQ3RefinedCarrierIndex : ℝ)⁻¹ *
            ∑ i : nativeHeatQ3RefinedCarrierIndex, ∑ d : Fin 9,
              nativeHeatQ3RefinedCarrierChildSignedOffDiagonalProfile
                M h m i d σ (fields i)) + 0 :=
          add_le_add hscaled hcenter'
      _ = nativeHeatQ3RefinedCarrierOffDiagonalFirstOrderRow M h m t r g z := by
        rw [hmeanActual, hfieldsProfile]
        simpa [Q, U, hU, hvol, σ, hnorm, add_zero] using hform
      _ = _ := hrow
  have hR : P₀ = R + I.comp C := by
    dsimp only [R]
    exact (sub_add_cancel P₀ (I.comp C)).symm
  have hgradEq := nativeHeatVHEATSourceGradientBracket_eq
    H hH P₀ R C I (fderiv ℝ μ fields) coeff θ hR
  have hgradEq' :
      (coeff / 2) *
        (modelGradientSquareTrace μ (fun j => P₀ (H j)) fields -
            (1 + θ) * modelGradientSquareTrace μ (fun j => I (C (H j))) fields) =
        -θ * centerGenerator H C I B + mixedGenerator H C I R B +
          (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) := by
    simpa only [modelGradientSquareTrace, ContinuousLinearMap.comp_apply,
      B] using hgradEq
  have hsourceBracket :=
    nativeHeatQ3RefinedCarrierSourceCenteredPowerBracket_le_profileRows
      M h hM m θ hθ fields r hr
  have hsourceBracket' :
      -θ * centerGenerator H C I B + mixedGenerator H C I R B +
          (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) ≤
        (coeff / 2) * ((1 + θ⁻¹) * sourceRows) := by
    simpa only [Q, U, hU, hvol, V, hV, σ, hσ, μ, I, C, L, P₀, R, D,
      coeff, B, H, sourceRows,
      nativeHeatQ3RefinedCarrierSourceRowsForFields,
      ContinuousLinearMap.comp_apply] using hsourceBracket.2
  have hBracket :
      (coeff / 2) *
          (modelGradientSquareTrace μ (fun j => P₀ (H j)) fields -
            (1 + θ) * modelGradientSquareTrace μ (fun j => I (C (H j))) fields) ≤
        (coeff / 2) * (1 + θ⁻¹) * sourceRows := by
    calc
      _ = -θ * centerGenerator H C I B + mixedGenerator H C I R B +
          (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) := hgradEq'
      _ ≤ (coeff / 2) * ((1 + θ⁻¹) * sourceRows) := hsourceBracket'
      _ = (coeff / 2) * (1 + θ⁻¹) * sourceRows := by ring
  calc
    nativeHeatQ3RefinedCarrierSourcePhysicalCancelledGeneratorIntegrand
        M h hM m θ t r z =
        (r : ℝ) * (μ fields) ^ ((r : ℝ) - 1) *
          ((1 / 2 : ℝ) * modelCovarianceTrace μ (fun j => P₀ (H j)) fields -
            ((1 + θ) / 2) * modelCovarianceTrace μ
              (fun j => I (C (H j))) fields) +
        (coeff / 2) *
          (modelGradientSquareTrace μ (fun j => P₀ (H j)) fields -
            (1 + θ) * modelGradientSquareTrace μ (fun j => I (C (H j))) fields) := hgenEq
    _ ≤ heatVHEATDriftRefinedPhysicalDrift M h m t r g z +
        (coeff / 2) * (1 + θ⁻¹) * sourceRows := add_le_add hFirst hBracket
    _ = _ := by rw [hcoeff]; ring

end
end ASDExplicitGamma.Native

end
