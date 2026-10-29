module

public import ASDExplicitGamma.Main.HotObsLocalRows
public import ASDExplicitGamma.Main.HotTrialExpectationsDrop
public import ASDExplicitGamma.Main.MixedBridgeDepthFive
public import ASDExplicitGamma.Inverse.MixedBridgeLocal

/-! Observer-root version of the unweighted local first-corrector moment of the hot
trial: `E V_U^2 <= xi - betaOld * a <= xi` for every cell `U` of the observer tiling
`descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)`, and for the tiling average. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic

noncomputable section

/-- Every depth-`hobs+5` cell of the observer root `originCube 2 (m+hobs)` (`hobs ≤ 40`) is a
bank observer root of depth five. -/
theorem hot_obs_cell_mem_bank_roots (m : ℤ) (hobs : ℕ) (h40 : hobs ≤ 40)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)) :
    U ∈ bankObserverRoots (originCube 2 (m + 40)) 5 := by
  have hparent : originCube 2 (m + hobs) ∈
      descendantsAtDepth (originCube 2 (m + 40)) (40 - hobs) := by
    have h := originCube_mem_descendantsAtDepth' 2 (m + 40) (40 - hobs)
    have e : m + 40 - ((40 - hobs : ℕ) : ℤ) = m + hobs := by
      push_cast [Nat.cast_sub h40]
      ring
    rwa [e] at h
  have hdepth := mem_descendantsAtDepth_add hparent hU
  have e2 : 40 - hobs + (hobs + 5) = 40 + 5 := by omega
  rw [e2] at hdepth
  exact hdepth

/-- Every cell of the observer tiling has scale `m - 5`. -/
theorem hot_obs_cell_scale (m : ℤ) (hobs : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)) :
    U.scale = m - ((5 : ℕ) : ℤ) := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
  simp only [originCube] at hs
  rw [hs]
  push_cast
  ring

/-- The observer tiling average of the local first-corrector squares. -/
def mainHotObsVl2 (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  descendantsAverage (originCube 2 (m + hobs)) (hobs + 5)
    (fun U => mixedBridgeVLocal M m U t ω ^ 2)

/-- Observer-root local corrector moment: for every cell `U` of the observer tiling,
`E V_U^2 <= xi - betaOld * a <= xi`, and the same for the tiling average. -/
theorem main_hot_obs_vl2_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) /
      (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
    (∀ U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5),
      U.scale = m - 5 ∧
      Integrable (fun ω => mixedBridgeVLocal M m U t ω ^ 2) μ ∧
      (∀ ω, 0 ≤ mixedBridgeVLocal M m U t ω ^ 2) ∧
      (∫ ω, mixedBridgeVLocal M m U t ω ^ 2 ∂μ) ≤
        xi - mainBetaOld * inSourceMeanActual M m 5 t ∧
      (∫ ω, mixedBridgeVLocal M m U t ω ^ 2 ∂μ) ≤ xi) ∧
    Integrable (mainHotObsVl2 M m hobs t) μ ∧
    (∀ ω, 0 ≤ mainHotObsVl2 M m hobs t ω) ∧
    (∫ ω, mainHotObsVl2 M m hobs t ω ∂μ) ≤
      xi - mainBetaOld * inSourceMeanActual M m 5 t ∧
    (∫ ω, mainHotObsVl2 M m hobs t ω ∂μ) ≤ xi := by
  classical
  intro μ v xi
  let Q := originCube 2 (m + hobs)
  let a := inSourceMeanActual M m 5 t
  have ha0 : 0 ≤ a :=
    (main_hot_energy_drop_identity M h hM hγ N hpast m hm t ht).2.2.1.trans
      (main_hot_energy_drop_identity M h hM hγ N hpast m hm t ht).2.2.2.1
  have hb0 : 0 ≤ mainBetaOld := by norm_num [mainBetaOld]
  have hrows (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q (hobs + 5)) :
      Integrable (fun ω => mixedBridgeVLocal M m U t ω ^ 2) μ ∧
      (∫ ω, mixedBridgeVLocal M m U t ω ^ 2 ∂μ) ≤ xi - mainBetaOld * a := by
    have hscale := hot_obs_cell_scale m hobs U hU
    have hroots := hot_obs_cell_mem_bank_roots m hobs h40 U hU
    have hr := mixed_bridge_local_parent_gap_rows''
      M h hM hγ N hpast m hm t ht U hscale hroots
    have hmean0 := (mixed_bridge_local_trace_mean'
      M h hM hγ N hpast m hm t ht 5 (by omega) U hscale 0).2
    have hmean : (∫ ω, rawCubeFourLoadTrace M m U t ω ∂μ) = a := by
      simpa only [mixedDepthTraceAverage,
        rawWeakTraceSequence_zero_eq_rawCubeFourLoadTrace] using hmean0
    refine ⟨hr.1, ?_⟩
    have h2 : (∫ ω, mixedBridgeVLocal M m U t ω ^ 2 ∂μ) ≤
        xi - mainBetaOld * ∫ ω, rawCubeFourLoadTrace M m U t ω ∂μ := hr.2.1
    rw [hmean] at h2
    exact h2
  have hne : (descendantsAtDepth Q (hobs + 5)).Nonempty := by
    have h0 := originCube_mem_descendantsAtDepth' 2 (m + hobs) (hobs + 5)
    exact ⟨_, h0⟩
  have hcard : (0 : ℝ) < ((descendantsAtDepth Q (hobs + 5)).card : ℝ) := by
    exact_mod_cast hne.card_pos
  have hfun : mainHotObsVl2 M m hobs t = fun ω =>
      ((descendantsAtDepth Q (hobs + 5)).card : ℝ)⁻¹ *
        ∑ U ∈ descendantsAtDepth Q (hobs + 5), mixedBridgeVLocal M m U t ω ^ 2 := rfl
  have hint : Integrable (mainHotObsVl2 M m hobs t) μ := by
    rw [hfun]
    exact (integrable_finsetSum _ fun U hU => (hrows U hU).1).const_mul _
  have hnn (ω : Cutoff.CutoffSample 2) : 0 ≤ mainHotObsVl2 M m hobs t ω := by
    rw [hfun]
    exact mul_nonneg (inv_nonneg.mpr hcard.le)
      (Finset.sum_nonneg fun U _ => sq_nonneg _)
  have hbound : (∫ ω, mainHotObsVl2 M m hobs t ω ∂μ) ≤ xi - mainBetaOld * a := by
    rw [hfun, integral_const_mul,
      integral_finsetSum _ fun U hU => (hrows U hU).1]
    calc
      ((descendantsAtDepth Q (hobs + 5)).card : ℝ)⁻¹ *
          ∑ U ∈ descendantsAtDepth Q (hobs + 5),
            ∫ ω, mixedBridgeVLocal M m U t ω ^ 2 ∂μ ≤
        ((descendantsAtDepth Q (hobs + 5)).card : ℝ)⁻¹ *
          ∑ U ∈ descendantsAtDepth Q (hobs + 5), (xi - mainBetaOld * a) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun U hU => (hrows U hU).2)
          (inv_nonneg.mpr hcard.le)
      _ = xi - mainBetaOld * a := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        field_simp
  refine ⟨fun U hU => ⟨?_, (hrows U hU).1, fun ω => sq_nonneg _, (hrows U hU).2, ?_⟩,
    hint, hnn, hbound, ?_⟩
  · have := hot_obs_cell_scale m hobs U hU
    simpa using this
  · nlinarith [mul_nonneg hb0 ha0, (hrows U hU).2]
  · nlinarith [mul_nonneg hb0 ha0]

end

end ASDExplicitGamma.Main
