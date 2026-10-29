module

public import ASDExplicitGamma.Main.HotEOscillationNode
public import ASDExplicitGamma.Main.HotEOscillationDepthFiveProfileOfHist
public import ASDExplicitGamma.Main.HotObsSplitOfHist
public import ASDExplicitGamma.Main.HotObsVl2OfHist

/-! Successors of `HotEOscillationNode` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response

noncomputable section

/-- Successor of `main_hot_e_oscillation` with the history envelope `Hfun`. -/
theorem main_hot_e_oscillation_ofHist
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) (b : ℝ) (hb : 0 < b)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let v := (q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2
    let xi := mainEnvelopeXi v M.gamma mainSourceInversePrefix (theta M) t
    let a := inSourceMeanActual M m 5 t
    let f := modelTraceHeatAverage (m + hobs) M m t
    let H := Hfun t
    (∫ ω, mainHotOscRow M m hobs t b ω ∂μ) ≤
      mainEOscillationSourceProfile
        (mainLoadD (b ^ 2) a f H xi (mainKd (b ^ 2))) H (mainOp (b ^ 2)) (mainOm (b ^ 2)) := by
  classical
  intro μ v xi a f H
  have hpast' : ∀ n ≤ m, nativeInductionState M h n := fun n hn => hpast n (lt_of_le_of_lt hn hm)
  let L := q3ModelLength (m + 1)
  let Bs : Cutoff.CutoffSample 2 → ℝ := mixedBridgeBstar M m t
  let Dr : Cutoff.CutoffSample 2 → ℝ := mainHotDropObs M m hobs t
  let V2 : Cutoff.CutoffSample 2 → ℝ := mainHotObsVl2 M m hobs t
  let S : Cutoff.CutoffSample 2 → ℝ := mainEoscDepthFiveShiftedJointProfileHot L hobs M m t b
  let Sa : Cutoff.CutoffSample 2 → ℝ := mainEoscDepthFiveActualJointProfileHot L hobs M m t b
  have hL := (hot_scale_eq m hobs).le
  have hprof := main_eosc_depth_five_shifted_joint_profile_hot_ofHist (Hfun := Hfun) (hHist := hHist) L hobs M h hM hγ m hL hpast' t ht
    b hb
  have hSle := main_eosc_actual_joint_profile_rms_le_shifted_hot L hobs M h hM hγ m hL hpast' t
    ht b
  have hsplit := main_hot_obs_positive_split_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ N hpast m hm hobs t ht
  have hbs : mixedGlobalHistoryMax M m t = Bs :=
    funext fun ω => main_hot_bstar_eq M m t ht ω
  rw [hbs] at hsplit
  have hV := main_hot_obs_vl2_moment_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ N hpast m hm hobs h1 h40 t ht
  have hBsNonneg : ∀ ω, 0 ≤ Bs ω := fun ω => mixed_bridge_bstar_nonneg M m t ω
  have hDrNonneg : ∀ ω, 0 ≤ Dr ω := fun ω => (main_hot_drop_obs_pathwise M m hobs t ω).2
  have hS0 : ∀ ω, 0 ≤ S ω := fun ω => Real.sqrt_nonneg _
  have hBD0 : ∀ ω, 0 ≤ Bs ω * Dr ω := fun ω => mul_nonneg (hBsNonneg ω) (hDrNonneg ω)
  obtain ⟨hI1, hC1⟩ := hot_integral_sqrt_mul_le μ (fun ω => Bs ω * Dr ω) S hBD0 hsplit.1
    hprof.1 hS0
  obtain ⟨hI2, hC2⟩ := hot_integral_sqrt_mul_le μ V2 S hV.2.2.1 hV.2.1 hprof.1 hS0
  have hq := hot_integral_sq_le_of_lpNorm μ S hprof.1 _ hprof.2
  have hka : 0 ≤ mainKa (b ^ 2) := by unfold mainKa mainA2; positivity
  have hkd : 0 ≤ mainKd (b ^ 2) := mainKd_nonneg _
  have hR1 : Real.sqrt (∫ ω, Bs ω * Dr ω ∂μ) ≤ mainR1 a f H := by
    unfold mainR1 mainHd
    exact Real.sqrt_le_sqrt hsplit.2.1
  have hT0 : Real.sqrt (∫ ω, V2 ω ∂μ) ≤ mainT0 xi := Real.sqrt_le_sqrt hV.2.2.2.2
  have hq0 : 0 ≤ Real.sqrt (∫ ω, S ω ^ 2 ∂μ) := Real.sqrt_nonneg _
  -- the pointwise domination
  have hdom : ∀ᵐ ω ∂μ, mainHotOscRow M m hobs t b ω ≤
      2 * mainKa (b ^ 2) * (Real.sqrt (Bs ω * Dr ω) * S ω) +
        2 * mainKd (b ^ 2) * (Real.sqrt (V2 ω) * S ω) := by
    filter_upwards [hSle] with ω hω
    have h0 := main_hot_osc_row_le_dom M m hobs h40 t ht b ω
    have hD : 0 ≤ mainKa (b ^ 2) * Real.sqrt (Bs ω * Dr ω) +
        mainKd (b ^ 2) * Real.sqrt (V2 ω) := by positivity
    have h2 : 2 * ((mainKa (b ^ 2) * Real.sqrt (Bs ω * Dr ω) +
        mainKd (b ^ 2) * Real.sqrt (V2 ω)) * Sa ω) ≤
        2 * ((mainKa (b ^ 2) * Real.sqrt (Bs ω * Dr ω) +
        mainKd (b ^ 2) * Real.sqrt (V2 ω)) * S ω) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hω hD) (by norm_num)
    have e : 2 * ((mainKa (b ^ 2) * Real.sqrt (Bs ω * Dr ω) +
        mainKd (b ^ 2) * Real.sqrt (V2 ω)) * S ω) =
        2 * mainKa (b ^ 2) * (Real.sqrt (Bs ω * Dr ω) * S ω) +
        2 * mainKd (b ^ 2) * (Real.sqrt (V2 ω) * S ω) := by ring
    exact h0.trans (h2.trans e.le)
  have hgInt : Integrable (fun ω => 2 * mainKa (b ^ 2) * (Real.sqrt (Bs ω * Dr ω) * S ω) +
      2 * mainKd (b ^ 2) * (Real.sqrt (V2 ω) * S ω)) μ :=
    (hI1.const_mul _).add (hI2.const_mul _)
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun ω => mainHotOscRow_nonneg M m hobs t b ω)) hgInt hdom
  rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  refine hmono.trans ?_
  have c1 := hC1.trans (mul_le_mul hR1 hq hq0 (Real.sqrt_nonneg _))
  have c2 := hC2.trans (mul_le_mul hT0 hq hq0 (Real.sqrt_nonneg _))
  have e1 := mul_le_mul_of_nonneg_left c1 (by positivity : 0 ≤ 2 * mainKa (b ^ 2))
  have e2 := mul_le_mul_of_nonneg_left c2 (by positivity : 0 ≤ 2 * mainKd (b ^ 2))
  unfold mainEOscillationSourceProfile mainLoadD
  linarith

end
end ASDExplicitGamma.Main
end
