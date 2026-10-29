module

public import ASDExplicitGamma.Native.HeatStepAllTimeField
public import ASDExplicitGamma.Native.HeatStepAllTimeFrame
public import ASDExplicitGamma.Native.HeatStepNode

/-! The all-time actual child cap of the refined heat step (source: refined child transport,
"Actual-time caps and common frame").

At the heat time `t` the child trace is viewed from the native cutoff `q`: shell `q+1` is fully
present and the further `ns` shells carry the amplitude `√t`.  The individual cooperative
comparison holds for every amplitude vector in `[0,1]` (weighted generator `∑ cᵢ² rowᵢ ≤ ∑ rowᵢ`),
so the gap `ns+1` individual cap applies; the sharp pathwise frame map `σ̄_q → σ̄_{q+1}` then gives
`y₀`.  The numerical comparison `individual ≤ old.x` for `9 ≤ ns ≤ 160` is a kernel check. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ASDExplicitGamma.Response
open scoped ENNReal

theorem nativeHeatStep_indiv_le_old (ns : ℕ) (h9 : 9 ≤ ns) (h160 : ns ≤ 160) :
    (nativeHeatIndividualGen ns).1 ≤ (nativeHeatOldRowGen ns).x := by
  have key : ∀ ns ∈ Finset.Icc 9 160,
      (nativeHeatIndividualGen ns).1 ≤ (nativeHeatOldRowGen ns).x := by decide +kernel
  exact key ns (Finset.mem_Icc.2 ⟨h9, h160⟩)

theorem nativeHeatStep_childAllTime_core (ns : ℕ) (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hind : NativeHeatStepIndivNum ns hns160) (hfr : NativeHeatStepFrameNum ns)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (q N : ℤ) (hN : q + 1 = N)
    (hpast : ∀ j < q, nativeInductionState M h j) (hstate : nativeInductionState M h q)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable q M.nu (Annealed.sigmaBar M N)
        (parentBoundaryObserverBandScalar q N ns t ω)) 20
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal ((nativeHeatY0Gen ns : ℚ) : ℝ) := by
  subst hN
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  let W := nativeHeatStepAmp q t ht.2.le
  let Xw : Cutoff.CutoffSample 2 → C(closure (cubeSet (originCube 2 q)), ℝ) := fun ω =>
    nativeSourceBandScalar_W W q (ns + 1) 1 ω
  have hXw (ω : Cutoff.CutoffSample 2) :
      Xw ω = parentBoundaryObserverBandScalar q (q + 1) ns t ω :=
    nativeHeatStep_weightedBand_eq q ns t ht.2.le ω
  have hσ0 := (Annealed.sigmaBar_characterization M q).1
  have hσ1 := (Annealed.sigmaBar_characterization M (q + 1)).1
  have hΦ0 := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu
    (Annealed.sigmaBar M q) M.nu_pos hσ0
  have hΦ1 := modelTraceObservable_hasPolynomiallyBoundedC2Derivatives q M.nu
    (Annealed.sigmaBar M (q + 1)) M.nu_pos hσ1
  have hXm : Measurable Xw := native_source_band_scalar_measurable_W (W := W) q (ns + 1) 1
  let T : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    modelTraceObservable q M.nu (Annealed.sigmaBar M q) (Xw ω)
  let Tn : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    modelTraceObservable q M.nu (Annealed.sigmaBar M (q + 1)) (Xw ω)
  have hTm : Measurable T := hΦ0.1.continuous.measurable.comp hXm
  have hTnm : Measurable Tn := hΦ1.1.continuous.measurable.comp hXm
  have hT0 : ∀ ω, 0 ≤ T ω := fun ω =>
    modelTraceObservable_nonneg q M.nu (Annealed.sigmaBar M q) M.nu_pos hσ0 _
  have hTn0 : ∀ ω, 0 ≤ Tn ω := fun ω =>
    modelTraceObservable_nonneg q M.nu (Annealed.sigmaBar M (q + 1)) M.nu_pos hσ1 _
  have hpath : ∀ ω, let rho : ℝ := (Annealed.sigmaBar M (q + 1) : ℝ) / (Annealed.sigmaBar M q : ℝ)
      Tn ω ≤ (rho + rho⁻¹) / 2 * T ω + (rho - rho⁻¹) / 2 * Real.sqrt (T ω * (T ω + 8)) +
        4 * ((rho + rho⁻¹) / 2 - 1) := by
    intro ω
    exact nativeHeatStep_sharpPathwise_field M q (originCube 2 q)
      (responsePlanarCoefficientField M.nu
        (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 q))) ℝ ℝ
          (Xw ω)))
      (responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet (originCube 2 q)) M.nu
        M.nu_pos _)
  have hmin : min (nativeHeatOldRowGen ns).x (nativeHeatIndividualGen ns).1 =
      (nativeHeatIndividualGen ns).1 :=
    min_eq_right (nativeHeatStep_indiv_le_old ns hns9 hns160)
  have hL : eLpNorm' T 20 μ ≤ ENNReal.ofReal ((nativeHeatShiftArgGen ns : ℚ) : ℝ) := by
    have h1 := nativeHeatStep_weighted_individual ns hns9 hns160 hind W M h hM hg q hpast hstate
    have hshift : nativeHeatShiftArgGen ns = (nativeHeatIndividualGen ns).1 := by
      unfold nativeHeatShiftArgGen
      exact hmin
    rw [hshift]
    exact h1
  have htq0 : (0 : ℝ) ≤ ((nativeHeatShiftArgGen ns : ℚ) : ℝ) := by
    have hv := heat_configured_individual_old_valid (nativeHeatIndexGen ns hns160)
    rw [hind.gap, hind.old_source] at hv
    have hx : (0 : ℚ) ≤ (nativeHeatOldRowGen ns).x := hv.2.1.le
    have hform := congrArg Prod.fst hind.indiv
    have hs := of_decide_eq_true hind.result20_root
    have hz := nativeConfiguredSystem_scale_pos (nativeHeatIndexGen ns hns160)
    have hA : (0 : ℚ) < nativeA := by norm_num [nativeA]
    have hprod : (0 : ℚ) ≤ nativeRootUp
        ((nativeConfiguredSystem (nativeHeatIndexGen ns hns160)).result.getD 20 0) 20 *
        (nativeConfiguredSystem (nativeHeatIndexGen ns hns160)).system.z * nativeA :=
      mul_nonneg (mul_nonneg hs.2.2.1 hz.le) hA.le
    have hi : (0 : ℚ) ≤ (nativeHeatIndividualGen ns).1 := by
      rw [hform]
      exact hprod.trans (nativeUp_ge _)
    have : (0 : ℚ) ≤ nativeHeatShiftArgGen ns := le_min hx hi
    exact_mod_cast this
  have hTr := nativeHeatStep_frameTransfer M hg q T Tn hTm hTnm hT0 hTn0 hpath
    (nativeHeatShiftArgGen ns) htq0 hfr.shift_root hL
  have hfun : (fun ω : Cutoff.CutoffSample 2 =>
      modelTraceObservable q M.nu (Annealed.sigmaBar M (q + 1))
        (parentBoundaryObserverBandScalar q (q + 1) ns t ω)) = Tn := by
    funext ω
    simp only [Tn, hXw]
  rw [hfun, eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hTnm.aestronglyMeasurable]
  have hy0 : nativeHeatY0Gen ns = nativeShiftedFrame 1 (nativeHeatShiftArgGen ns) := rfl
  rw [hy0]
  simpa using hTr

end ASDExplicitGamma.Native
