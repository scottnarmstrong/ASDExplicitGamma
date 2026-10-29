module

public import ASDExplicitGamma.Main.ThetaGeneratorFinal
public import ASDExplicitGamma.Main.ThetaGeneratorPanelEnclosure
public import ASDExplicitGamma.Main.FrameEndpoint
public import ASDExplicitGamma.Numerics.MainReturnCertificate.Composition

/-! MA-THETA-CONTINUATION: the `γ₀` panel/chronology composition applied to `f/θ`. For the actual
model at `γ ≤ γ₀`, `θ = γ/γ₀`: if the completed ordinary mean at label `m` is at most `θ x₀/G`, the
completed mean at label `m+1` is at most `θ · advanceInsertion x₀ cert / G`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set MeasureTheory ASDExplicitGamma.Numerics ASDExplicitGamma.Numerics.Mirror
open ASDExplicitGamma.Numerics.MainReturnCertificate
open ASDExplicitGamma.Numerics.Spike
open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Inverse ASDExplicitGamma

noncomputable section

/-- The panel record embedded in a `MainReturnCertificate` endpoint. -/
def thetaPanelCert (e : PanelEndpoints) : PanelCert :=
  { aUpper := e.aUpper, ellLower := e.ellLower,
    rhoLower := e.rhoLower, rhoUpper := e.rhoUpper,
    offsetLower := e.offsetLower, offsetUpper := e.offsetUpper,
    supportELower := e.supportELower, supportEUpper := e.supportEUpper,
    supportLambdaLower := e.supportLambdaLower,
    supportLambdaUpper := e.supportLambdaUpper,
    supportJLower := e.supportJLower, supportJUpper := e.supportJUpper }

/-- Grid step from the real endpoint recurrence. -/
theorem main_panel_grid_advance_of_endpoint_bound_Th
    (e : PanelEndpoints) (x : ℕ) {fa fb : ℝ}
    (hreal : fb ≤ (e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) * fa +
      (e.offsetUpper : ℝ) / (Spike.gridScale : ℝ))
    (hstart : fa ≤ (x : ℝ) / (Spike.gridScale : ℝ)) :
    fb ≤ (advancePanel x (thetaPanelCert e) : ℝ) /
      (Spike.gridScale : ℝ) := by
  have hG : 0 < (Spike.gridScale : ℝ) := by norm_num [Spike.gridScale]
  have hGnat : 0 < Spike.gridScale := by norm_num [Spike.gridScale]
  have hrho : 0 ≤ (e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hstart hrho
  have hceil := div_le_ceilDiv hGnat (a := x * e.rhoUpper)
  have hceil' : ((x * e.rhoUpper : ℕ) : ℝ) /
      (Spike.gridScale : ℝ) / (Spike.gridScale : ℝ) ≤
      (ceilDiv (x * e.rhoUpper) Spike.gridScale : ℝ) / (Spike.gridScale : ℝ) :=
    div_le_div_of_nonneg_right hceil hG.le
  have hscale : (e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) *
      ((x : ℝ) / (Spike.gridScale : ℝ)) =
      ((x * e.rhoUpper : ℕ) : ℝ) / (Spike.gridScale : ℝ) / (Spike.gridScale : ℝ) := by
    push_cast
    ring
  have hgrid :
      (ceilGridProduct x e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) +
      (e.offsetUpper : ℝ) / (Spike.gridScale : ℝ) =
      (advancePanel x (thetaPanelCert e) : ℝ) / (Spike.gridScale : ℝ) := by
    simp [advancePanel, ceilGridProduct, thetaPanelCert,
      Nat.cast_add, add_div]
  calc
    fb ≤ (e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) * fa +
        (e.offsetUpper : ℝ) / (Spike.gridScale : ℝ) := hreal
    _ ≤ (e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) * ((x : ℝ) / (Spike.gridScale : ℝ)) +
        (e.offsetUpper : ℝ) / (Spike.gridScale : ℝ) := add_le_add hmul le_rfl
    _ = ((x * e.rhoUpper : ℕ) : ℝ) / (Spike.gridScale : ℝ) / (Spike.gridScale : ℝ) +
        (e.offsetUpper : ℝ) / (Spike.gridScale : ℝ) := by rw [hscale]
    _ ≤ (ceilGridProduct x e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) +
        (e.offsetUpper : ℝ) / (Spike.gridScale : ℝ) := add_le_add hceil' le_rfl
    _ = _ := hgrid

/-- Eight panel endpoint recurrences fold into the integer recurrence. -/
theorem main_eight_panel_grid_fold_of_endpoint_Th
    (f : ℝ → ℝ) (e : ℕ → PanelEndpoints) (x : ℕ → ℕ)
    (hstart : f 0 ≤ (x 0 : ℝ) / (Spike.gridScale : ℝ))
    (hnext : ∀ j : ℕ, j < 8 → x (j + 1) = advancePanel (x j)
      (thetaPanelCert (e j)))
    (hend : ∀ j : ℕ, j < 8 → f (((j + 1 : ℕ) : ℝ) / 8) ≤
      (e j).rhoUpper / (Spike.gridScale : ℝ) * f ((j : ℝ) / 8) +
        (e j).offsetUpper / (Spike.gridScale : ℝ)) :
    f 1 ≤ (x 8 : ℝ) / (Spike.gridScale : ℝ) := by
  have hbound : ∀ (j : ℕ), j ≤ 8 →
      f ((j : ℝ) / 8) ≤ (x j : ℝ) / (Spike.gridScale : ℝ) := by
    intro j hj
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
        have hj8 : j < 8 := by omega
        rw [hnext j hj8]
        exact main_panel_grid_advance_of_endpoint_bound_Th (e j) (x j)
          (hend j hj8) (ih (by omega))
  have hlast := hbound 8 le_rfl
  norm_num at hlast ⊢
  exact hlast

/-- At time `0` the heat average is the completed OLD mean. -/
theorem modelTraceHeatAverage_zero_eq_Th (q : ℤ) (M : ABKModel 2) (m : ℤ) :
    modelTraceHeatAverage q M m 0 =
      ∫ ω, cutoffTraceDefect M m q ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hpath (ω : Cutoff.CutoffSample 2) :
      traceDefect (cubeSet (originCube 2 q))
          (Model.partialInsertedCoefficient M m 0 ω).toFun
          (Annealed.sigmaBar M m : ℝ) = cutoffTraceDefect M m q ω := by
    have hcoeff : (Model.partialInsertedCoefficient M m 0 ω).toFun =
        (Cutoff.coefficientCutoff M.nu m ω).toFun := by
      ext x i j
      simp [Model.partialInsertedCoefficient]
    rw [cutoffTraceDefect, hcoeff]
  rw [modelTraceHeatAverage]
  exact integral_congr_ae (Filter.Eventually.of_forall hpath)

theorem frame_ceil_step_Th (frameUpper x : ℕ) {t : ℝ}
    (ht : t ≤ (x : ℝ) / (Spike.gridScale : ℝ)) :
    (frameUpper : ℝ) / (Spike.gridScale : ℝ) * t ≤
      (ceilGridProduct x frameUpper : ℝ) / (Spike.gridScale : ℝ) := by
  have hG : 0 < (Spike.gridScale : ℝ) := by norm_num [Spike.gridScale]
  have hGnat : 0 < Spike.gridScale := by norm_num [Spike.gridScale]
  have hfactor : 0 ≤ (frameUpper : ℝ) / (Spike.gridScale : ℝ) := by positivity
  have hceil := div_le_ceilDiv hGnat (a := x * frameUpper)
  have hceil' : ((x * frameUpper : ℕ) : ℝ) /
      (Spike.gridScale : ℝ) / (Spike.gridScale : ℝ) ≤
      (ceilDiv (x * frameUpper) Spike.gridScale : ℝ) / (Spike.gridScale : ℝ) :=
    div_le_div_of_nonneg_right hceil hG.le
  have hscale : (frameUpper : ℝ) / (Spike.gridScale : ℝ) *
      ((x : ℝ) / (Spike.gridScale : ℝ)) =
      ((x * frameUpper : ℕ) : ℝ) / (Spike.gridScale : ℝ) / (Spike.gridScale : ℝ) := by
    push_cast
    ring
  calc
    _ ≤ (frameUpper : ℝ) / (Spike.gridScale : ℝ) * ((x : ℝ) / (Spike.gridScale : ℝ)) :=
        mul_le_mul_of_nonneg_left ht hfactor
    _ = _ := hscale
    _ ≤ _ := by simpa only [ceilGridProduct] using hceil'

theorem main_panel_grid_recurrence_eq_range_fold_Th
    (e : ℕ → PanelEndpoints) (x : ℕ → ℕ)
    (hnext : ∀ j : ℕ, j < 8 → x (j + 1) = advancePanel (x j)
      (thetaPanelCert (e j))) :
    x 8 = (List.range 8).foldl
      (fun value j => advancePanel value (thetaPanelCert (e j))) (x 0) := by
  let step : ℕ → ℕ → ℕ := fun value j =>
    advancePanel value (thetaPanelCert (e j))
  have hfold : ∀ (j : ℕ), j ≤ 8 →
      x j = (List.range j).foldl step (x 0) := by
    intro j hj
    induction j with
    | zero => simp [step]
    | succ j ih =>
        have hj8 : j < 8 := by omega
        calc
          x (j + 1) = advancePanel (x j)
              (thetaPanelCert (e j)) := hnext j hj8
          _ = step ((List.range j).foldl step (x 0)) j := by
              rw [ih (by omega)]
          _ = (List.range (j + 1)).foldl step (x 0) := by
              simp [step, List.range_succ, List.foldl_append]
  simpa [step] using hfold 8 le_rfl


/-- The `γ`-actual trace heat average divided by `θ` has the `ObsChronoV35` shape at `γ₀`. -/
theorem theta_chrono_shape
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40) :
    AbsolutelyContinuousOnInterval
        (fun s => (theta M)⁻¹ * modelTraceHeatAverage (m + (hobs : ℤ)) M m s) 0 1 ∧
      ThetaChronoShape
        (fun s => (theta M)⁻¹ * modelTraceHeatAverage (m + (hobs : ℤ)) M m s) hobs := by
  have hmain := ma_theta_generator_observer_node M h hM hγ N hpast m hm hobs h1 h40
  dsimp only at hmain
  obtain ⟨hAC, hdom, hder⟩ := hmain
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hθpos : 0 < theta M := by
    show 0 < M.gamma / gammaZero
    exact div_pos hgpos (by norm_num [gammaZero])
  refine ⟨hAC.const_mul _, ?_, ?_⟩
  · intro s hs
    simpa only [inv_mul_eq_div] using hdom s hs
  · filter_upwards [hder] with s hs hs01
    have hd := hs hs01
    rw [deriv_const_mul_field']
    simp only [inv_mul_eq_div]
    have e1 : mainAffineTermGamma0 (mainAffineFlatBoundaryCapQ (hobs - 1)) s =
        panelVbar / 2 * mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s +
          panelVbar * mainAffineFlatBoundaryCapQ (hobs - 1) * (mainBeta - 1) +
          (4 + 2 * Real.sqrt 2) * (156 / 5 : ℝ) * mainA2 panelVbar / 9 := by
      unfold mainAffineTermGamma0 panelVbar
      rw [show (31.2 : ℝ) = 156 / 5 by norm_num]
    rw [e1] at hd
    rw [div_le_iff₀ hθpos]
    refine hd.trans (le_of_eq ?_)
    ring_nf

/-- MA-THETA-CONTINUATION, one insertion: the `γ₀` panel/chronology composition applied to `f/θ`.
From the completed mean at label `m` bounded by `θ x₀/G`, the completed mean at label `m+1` on the
observer cube `m + hobs` is bounded by `θ · advanceInsertion x₀ cert / G`. -/
theorem ma_theta_insertion_step (hL : PanelLeafL1L2)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40)
    (cert : InsertionCert)
    (hframe : insertionFrameRecurrenceFields cert.frameLower cert.frameUpper)
    (e : ℕ → PanelEndpoints)
    (hcert : cert.panels = (List.range 8).map (fun j => thetaPanelCert (e j)))
    (x0 : ℕ)
    (hOld : (∫ ω, cutoffTraceDefect M m (m + (hobs : ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M * ((x0 : ℝ) / (Spike.gridScale : ℝ)))
    (hpanels : ∀ j : ℕ, j < 8 → ∃ d : MainPanelData,
      panelFormulaBounds d (e j) ∧ panelRecurrenceFields (e j) ∧ d.anchor = 1 / 100 ∧
      (d.initialMean : ℝ) = mainSourceMeanPrefix ∧
      (d.initialInverseMean : ℝ) = mainSourceInversePrefix + 1 / 10 ^ 12 ∧
      (d.covarianceCap : ℝ) = mainAffineFlatBoundaryCapQ (hobs - 1) ∧
      ∀ s ∈ Icc ((j : ℝ) / 8) (((j + 1 : ℕ) : ℝ) / 8), QInterval.Contains d.time s) :
    (∫ ω, cutoffTraceDefect M (m + 1) (m + (hobs : ℤ)) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M * ((advanceInsertion x0 cert : ℝ) / (Spike.gridScale : ℝ)) := by
  obtain ⟨hAC, hshape⟩ := theta_chrono_shape M h hM hγ N hpast m hm hobs h1 h40
  set f := modelTraceHeatAverage (m + (hobs : ℤ)) M m with hf
  set u : ℝ → ℝ := fun s => (theta M)⁻¹ * f s with hu
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hθpos : 0 < theta M := by
    show 0 < M.gamma / gammaZero
    exact div_pos hgpos (by norm_num [gammaZero])
  have hG : 0 < (Spike.gridScale : ℝ) := by norm_num [Spike.gridScale]
  have hend : ∀ j : ℕ, j < 8 → u (((j + 1 : ℕ) : ℝ) / 8) ≤
      (e j).rhoUpper / (Spike.gridScale : ℝ) * u ((j : ℝ) / 8) +
        (e j).offsetUpper / (Spike.gridScale : ℝ) := by
    intro j hj
    obtain ⟨d, hb, hfields, hanchor, hmean, hxi, hq, hdsub⟩ := hpanels j hj
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / 8 := by positivity
    have hj1 : (((j + 1 : ℕ) : ℝ) / 8) ≤ 1 := by
      have : ((j + 1 : ℕ) : ℝ) ≤ 8 := by exact_mod_cast hj
      linarith
    exact panel_endpoint_Th hL u hobs hshape hAC d (e j) hb hfields hanchor hmean hxi hq
      (a := (j : ℝ) / 8) (b := ((j + 1 : ℕ) : ℝ) / 8)
      (by push_cast; linarith) (by push_cast; ring) hj0 hj1 hdsub
  obtain ⟨x, hx0, hnext⟩ : ∃ x : ℕ → ℕ, x 0 = x0 ∧ ∀ j : ℕ, j < 8 →
      x (j + 1) = advancePanel (x j) (thetaPanelCert (e j)) :=
    ⟨fun j => Nat.rec x0 (fun i v => advancePanel v (thetaPanelCert (e i))) j,
      rfl, fun j _ => rfl⟩
  have hstart : u 0 ≤ ((x 0 : ℕ) : ℝ) / (Spike.gridScale : ℝ) := by
    simp only [hu, hf, modelTraceHeatAverage_zero_eq_Th, hx0]
    rw [inv_mul_le_iff₀ hθpos]
    simpa [mul_comm] using hOld
  have hpanels8 := main_eight_panel_grid_fold_of_endpoint_Th u e x hstart hnext hend
  have hratio := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity M m 1 (by norm_num)
  have hratio' :
      1 ≤ (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ) ∧
      (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ) ≤
        Real.rpow 3 (2 * M.gamma) := by
    simpa using hratio
  have hexponent : 2 * M.gamma ≤ (mainReturnFrameExponent : ℚ) := by
    have hframeExponent : (mainReturnFrameExponent : ℝ) = 2 * ASDExplicitGamma.gammaZero := by
      norm_num [mainReturnFrameExponent, ASDExplicitGamma.gammaZero]
    rw [hframeExponent]
    nlinarith [hγ]
  have hpower := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexponent
  have hframeUpper : Real.rpow 3 (2 * M.gamma) ≤
      (cert.frameUpper : ℝ) / (Spike.gridScale : ℝ) := hpower.trans hframe.2
  have hret := main_completed_endpoint_return_of_ratio M m (m + (hobs : ℤ))
    ((cert.frameUpper : ℝ) / (Spike.gridScale : ℝ)) hratio'.1 (hratio'.2.trans hframeUpper)
  have hstep := frame_ceil_step_Th cert.frameUpper (x 8) (t := u 1) (by simpa using hpanels8)
  have hfold : cert.panels.foldl advancePanel x0 = x 8 := by
    have hfold := main_panel_grid_recurrence_eq_range_fold_Th e x hnext
    rw [hcert, List.foldl_map]
    rw [hx0] at hfold
    exact hfold.symm
  have hf1 : 0 ≤ f 1 := by
    have hs' := hshape
    simp only [ThetaChronoShape] at hs'
    have := (hs'.1 1 ⟨zero_le_one, le_rfl⟩).1
    have h2 : (theta M)⁻¹ * f 1 ≥ 0 := this
    exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hθpos)).mp h2
  have hfu : f 1 = theta M * u 1 := by
    simp only [hu]; field_simp
  have hfU : 0 ≤ (cert.frameUpper : ℝ) / (Spike.gridScale : ℝ) := by positivity
  refine hret.trans ?_
  simp only [advanceInsertion, hfold]
  calc (cert.frameUpper : ℝ) / (Spike.gridScale : ℝ) * f 1
      = theta M * ((cert.frameUpper : ℝ) / (Spike.gridScale : ℝ) * u 1) := by
        rw [hfu]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hstep hθpos.le

end

end ASDExplicitGamma.Main
