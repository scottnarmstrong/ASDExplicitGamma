module

public import ASDExplicitGamma.Gaussian.GaussCentering
public import ASDExplicitGamma.Gaussian.ModelHeatPower
public import ASDExplicitGamma.Native.HeatVHEATBracket
public import ASDExplicitGamma.Native.HeatVHEATRefinedCarrier
public import ASDExplicitGamma.Native.HeatVHEATRefinedAssembly

/-! The exact VHEAT center cancellation and residual Young split for the
unscaled source center carrier. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Model
open scoped Topology

noncomputable section

local instance nativeHeatQ3RefinedSourceIndexNeZero :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance nativeHeatQ3RefinedSourceDomainCompact (m : ℤ) :
    CompactSpace (nativeHeatQ3RefinedCarrierDomain m) := by
  apply isCompact_iff_compactSpace.mp
  apply isCompact_iUnion
  intro i
  exact (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatQ3RefinedSourceChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatQ3RefinedSourceChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- On the physical refined-shell series, the unscaled source center gives
the exact backward-generator identity with the full `(1+θ)` center power
generator. -/
theorem nativeHeatQ3RefinedCarrierSourceCenterCancelledPowerGenerator_eq
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (σ : ℝ) (hσ : 0 < σ) (θ : ℝ)
    (k : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (c : nativeHeatQ3RefinedCarrierIndex → ℝ) (r : ℕ) (hr : 2 ≤ r) :
    let Q : nativeHeatQ3RefinedCarrierIndex → TriadicCube 2 :=
      fun i => nativeHeatQ3RefinedCarrierChild m i
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => cubeSet (Q i)
    let hU : ∀ i, MeasurableSet (U i) := fun i => measurableSet_cubeSet (Q i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal := fun i => volume_cubeSet_toReal_pos (Q i)
    let I := childConstantMap (fun i => closure (U i))
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos hσ
    let S := nativeHeatQ3RefinedCarrierFreshShellSeriesFactor M h hM m
    let W := nativeHeatQ3RefinedCarrierFreshShellSeriesDirections M h hM m
    let P := (nativeHeatQ3RefinedCarrierOldMap m).comp S
    let C₀ := (childCenterMap (nativeHeatQ3RefinedCarrierCenter m)).comp S
    let y := k + I c
    cancelledGenerator W P C₀ I (fun f => μ f ^ r) θ y =
      modelPowerHeatGenerator μ (fun j => P (W j)) (r : ℝ) y -
        (1 + θ) * modelPowerHeatGenerator μ
          (fun j => I (C₀ (W j))) (r : ℝ) y := by
  classical
  intro Q U hU hvol I μ S W P C₀ y
  let Φ : (∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) → ℝ :=
    fun f => μ f ^ r
  have hW : Summable (fun j => ‖W j‖ ^ 2) :=
    nativeHeatQ3RefinedCarrierFreshShellSeriesSummable M h hM m
  have hμpoly : HasPolynomiallyBoundedC2Derivatives μ := by
    simpa [μ] using childMeanTrace_polynomial U hU hvol M.nu σ M.nu_pos hσ
  have hμnonneg : ∀ z, 0 ≤ μ z := by
    intro z
    change 0 ≤ childMeanTrace U hU hvol M.nu σ M.nu_pos hσ z
    exact nativeHeat_childMeanTrace_nonneg Q M.nu σ M.nu_pos hσ z
  have hΦC2 : ContDiff ℝ 2 Φ := by
    dsimp [Φ]
    exact hμpoly.1.pow r
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hpowFn : (fun z => μ z ^ (r : ℝ)) = fun z => μ z ^ r := by
    funext z
    exact Real.rpow_natCast (μ z) r
  have hcancel :
      cancelledGenerator W P C₀ I Φ θ y =
        (1 / 2 : ℝ) * modelCovarianceTrace Φ (fun j => P (W j)) y -
          ((1 + θ) / 2) * modelCovarianceTrace Φ
            (fun j => I (C₀ (W j))) y := by
    calc
      _ = backwardGenerator Φ (fun j => P (W j))
          (fun j => I (C₀ (W j))) θ y := by
            exact (congrFun
              (generator_cancellation hW P C₀ I hΦC2 θ) y).symm
      _ = _ := rfl
  have hpowOld := modelCovarianceTrace_rpow hW P μ hμpoly hμnonneg hrR y
  have hpowCenter := modelCovarianceTrace_rpow hW (I.comp C₀) μ
    hμpoly hμnonneg hrR y
  have hpowOld' : (1 / 2 : ℝ) * modelCovarianceTrace Φ
      (fun j => P (W j)) y = modelPowerHeatGenerator μ
        (fun j => P (W j)) (r : ℝ) y := by
    change (1 / 2 : ℝ) * modelCovarianceTrace
      (fun z => μ z ^ r) (fun j => P (W j)) y = _
    rw [← hpowFn]
    exact hpowOld
  have hpowCenter' : (1 / 2 : ℝ) * modelCovarianceTrace Φ
      (fun j => I (C₀ (W j))) y = modelPowerHeatGenerator μ
        (fun j => I (C₀ (W j))) (r : ℝ) y := by
    change (1 / 2 : ℝ) * modelCovarianceTrace
      (fun z => μ z ^ r) (fun j => I (C₀ (W j))) y = _
    rw [← hpowFn]
    exact hpowCenter
  calc
    _ = (1 / 2 : ℝ) * modelCovarianceTrace Φ
          (fun j => P (W j)) y -
        (1 + θ) * ((1 / 2 : ℝ) * modelCovarianceTrace Φ
          (fun j => I (C₀ (W j))) y) := by
          rw [hcancel]
          ring
    _ = _ := by rw [hpowOld', hpowCenter']

/-- The unscaled source-center rank-one term splits into its centered
remainder, the center/remainder cross term, and the negative excess center
term. Young's inequality cancels that excess exactly, leaving no center-clock
payment. -/
theorem nativeHeatQ3RefinedCarrierSourceCenterRankOneResidualSplit
    (M : ABKModel 2) (m : ℤ) (θ : ℝ) (hθ : 0 < θ)
    (H : ℕ → C(nativeHeatQ3RefinedCarrierDomain m, ℝ))
    (hH : Summable (fun j => ‖H j‖ ^ 2))
    (x : ∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ))
    (r : ℕ) (hr : 2 ≤ r) :
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
      fun i => cubeSet (nativeHeatQ3RefinedCarrierChild m i)
    let hU : ∀ i, MeasurableSet (U i) :=
      fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i)
    let hvol : ∀ i, 0 < (volume (U i)).toReal :=
      fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i)
    let V : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) := fun i => closure (U i)
    let hV : ∀ i, V i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
      nativeHeatQ3RefinedCarrierChild_closure_subset m
    let σ : ℝ := Annealed.sigmaBar M (m + 1)
    let μ := childMeanTrace U hU hvol M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M (m + 1)).1
    let I : (nativeHeatQ3RefinedCarrierIndex → ℝ) →L[ℝ]
        (∀ i, C(V i, ℝ)) := childConstantMap V
    let C₀ : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ]
        (nativeHeatQ3RefinedCarrierIndex → ℝ) :=
      childCenterMap (nativeHeatQ3RefinedCarrierCenter m)
    let P := nativeHeatQ3RefinedCarrierOldMap m
    let R₀ : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ]
        (∀ i, C(V i, ℝ)) :=
      childRemainderMap V hV (nativeHeatQ3RefinedCarrierCenter m)
    let R := P - I.comp C₀
    let D := fderiv ℝ μ x
    let coeff := (r : ℝ) * ((r : ℝ) - 1) * (μ x) ^ (r - 2)
    let B : (∀ i, C(V i, ℝ)) →L[ℝ] (∀ i, C(V i, ℝ)) →L[ℝ] ℝ :=
      coeff • D.smulRight D
    let a : ℕ → ℝ := fun j => D (I (C₀ (H j)))
    let b : ℕ → ℝ := fun j => D (R₀ (H j));
    (-θ * centerGenerator H C₀ I B +
      mixedGenerator H C₀ I R B +
      (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j))) =
        coeff * (-(θ / 2) * ∑' j, (a j) ^ 2 +
          ∑' j, a j * b j + (1 / 2 : ℝ) * ∑' j, (b j) ^ 2) ∧
    (-θ * centerGenerator H C₀ I B +
      mixedGenerator H C₀ I R B +
      (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) ≤
        (coeff / 2) * ((1 + θ⁻¹) * ∑' j, (b j) ^ 2)) := by
  classical
  intro U hU hvol V hV σ μ I C₀ P R₀ R D coeff B a b
  let Acenter : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ] ℝ :=
    D.comp (I.comp C₀)
  let Arem : C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ] ℝ :=
    D.comp R₀
  have hR : R = R₀ := by
    ext f i y
    simp [R, R₀, P, I, C₀, V,
      nativeHeatQ3RefinedCarrierOldMap, childRemainderMap,
      childRestrictionMap, childConstantMap, childCenterMap,
      ContinuousLinearMap.comp_apply]
  have hμpoly : HasPolynomiallyBoundedC2Derivatives μ := by
    simpa [μ] using childMeanTrace_polynomial U hU hvol M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M (m + 1)).1
  have hμnonneg : ∀ z, 0 ≤ μ z := by
    intro z
    change 0 ≤ childMeanTrace U hU hvol M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M (m + 1)).1 z
    exact nativeHeat_childMeanTrace_nonneg
      (nativeHeatQ3RefinedCarrierChild m) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M (m + 1)).1 z
  have hcoeff : 0 ≤ coeff := by
    dsimp [coeff]
    have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hμpow : 0 ≤ (μ x) ^ (r - 2) := pow_nonneg (hμnonneg x) _
    exact mul_nonneg
      (mul_nonneg (by positivity) (by linarith)) hμpow
  have ha : Summable (fun j => (a j) ^ 2) := by
    have h := summable_sq_norm_map hH Acenter
    simpa only [a, Acenter, ContinuousLinearMap.comp_apply,
      Real.norm_eq_abs, sq_abs] using h
  have hb : Summable (fun j => (b j) ^ 2) := by
    have h := summable_sq_norm_map hH Arem
    simpa only [b, Arem, ContinuousLinearMap.comp_apply,
      Real.norm_eq_abs, sq_abs] using h
  let mulB : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ ℝ)
  have hab : Summable (fun j => a j * b j) := by
    have h := summable_bilinear_images hH mulB Acenter Arem
    simpa only [mulB, a, b, Acenter, Arem,
      ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul] using h
  have hcenter (j : ℕ) : D (I (C₀ (H j))) = a j := rfl
  have hresidual (j : ℕ) : D (R (H j)) = b j := by
    rw [hR]
  have hB (u v : ∀ i : nativeHeatQ3RefinedCarrierIndex, C(V i, ℝ)) :
      B u v = coeff * D u * D v := by
    simp only [B, ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
    ring
  have hcenterPoint (j : ℕ) :
      B (I (C₀ (H j))) (I (C₀ (H j))) = coeff * (a j) ^ 2 := by
    rw [hB, hcenter]
    ring
  have hcenterSum :
      (∑' j, B (I (C₀ (H j))) (I (C₀ (H j)))) =
        coeff * (∑' j, (a j) ^ 2) := by
    calc
      _ = ∑' j, coeff * (a j) ^ 2 := tsum_congr hcenterPoint
      _ = _ := tsum_mul_left
  have hcenterGen :
      centerGenerator H C₀ I B =
        (coeff / 2) * (∑' j, (a j) ^ 2) := by
    have h := center_generator_eq hH C₀ I B
    rw [hcenterSum] at h
    nlinarith [h]
  have hmixedPoint (j : ℕ) :
      B (I (C₀ (H j))) (R (H j)) = coeff * (a j * b j) := by
    rw [hB, hcenter, hresidual]
    ring
  have hmixedGen :
      mixedGenerator H C₀ I R B = coeff * (∑' j, a j * b j) := by
    calc
      _ = ∑' j, B (I (C₀ (H j))) (R (H j)) :=
        (mixed_generator_eq H C₀ I R B).symm
      _ = ∑' j, coeff * (a j * b j) := tsum_congr hmixedPoint
      _ = _ := tsum_mul_left
  have hresidualPoint (j : ℕ) :
      B (R (H j)) (R (H j)) = coeff * (b j) ^ 2 := by
    rw [hB, hresidual]
    ring
  have hresidualGen :
      (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) =
        (coeff / 2) * (∑' j, (b j) ^ 2) := by
    calc
      _ = (1 / 2 : ℝ) * ∑' j, coeff * (b j) ^ 2 := by
        rw [tsum_congr hresidualPoint]
      _ = _ := by rw [tsum_mul_left]; ring
  have hleft :
      -θ * centerGenerator H C₀ I B +
        mixedGenerator H C₀ I R B +
        (1 / 2 : ℝ) * ∑' j, B (R (H j)) (R (H j)) =
      coeff * (-(θ / 2) * ∑' j, (a j) ^ 2 +
        ∑' j, a j * b j + (1 / 2 : ℝ) * ∑' j, (b j) ^ 2) := by
    rw [hcenterGen, hmixedGen, hresidualGen]
    ring
  have hYoungCore := nativeHeat_summable_young_tsum ha hb hab θ hθ
  have hYoungHalf := mul_le_mul_of_nonneg_left hYoungCore
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hYoung :
      -(θ / 2) * ∑' j, (a j) ^ 2 +
        ∑' j, a j * b j + (1 / 2 : ℝ) * ∑' j, (b j) ^ 2 ≤
      ((1 + θ⁻¹) / 2) * ∑' j, (b j) ^ 2 := by
    calc
      _ = (1 / 2 : ℝ) *
          (-θ * (∑' j, (a j) ^ 2) +
            2 * (∑' j, a j * b j) + ∑' j, (b j) ^ 2) := by ring
      _ ≤ (1 / 2 : ℝ) * ((1 + θ⁻¹) * ∑' j, (b j) ^ 2) := hYoungHalf
      _ = _ := by ring
  refine ⟨hleft, ?_⟩
  calc
    _ = coeff * (-(θ / 2) * ∑' j, (a j) ^ 2 +
        ∑' j, a j * b j + (1 / 2 : ℝ) * ∑' j, (b j) ^ 2) := hleft
    _ ≤ coeff * (((1 + θ⁻¹) / 2) * ∑' j, (b j) ^ 2) :=
      mul_le_mul_of_nonneg_left hYoung hcoeff
    _ = (coeff / 2) * ((1 + θ⁻¹) * ∑' j, (b j) ^ 2) := by ring

end
end ASDExplicitGamma.Native

end
