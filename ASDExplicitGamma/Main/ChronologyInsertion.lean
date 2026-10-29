module

public import ASDExplicitGamma.Main.ChronologyPanel
public import ASDExplicitGamma.Main.FrameEndpoint
public import ASDExplicitGamma.Numerics.MainReturnCertificate.Composition

/-! Chronology: one insertion in endpoint form. The analytic input is the panel
endpoint recurrence `f b ≤ ρ/G · f a + off/G` (w02's `panel_endpoint`); the output is the
`advanceInsertion` grid step for the completed ordinary-mean trace. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set MeasureTheory ASDExplicitGamma.Numerics
open ASDExplicitGamma.Numerics.MainReturnCertificate
open ASDExplicitGamma.Numerics.Spike
open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian

/-- Grid step from the real endpoint recurrence. -/
theorem main_panel_grid_advance_of_endpoint_bound
    (e : PanelEndpoints) (x : ℕ) {fa fb : ℝ}
    (hreal : fb ≤ (e.rhoUpper : ℝ) / (Spike.gridScale : ℝ) * fa +
      (e.offsetUpper : ℝ) / (Spike.gridScale : ℝ))
    (hstart : fa ≤ (x : ℝ) / (Spike.gridScale : ℝ)) :
    fb ≤ (advancePanel x (mainPanelCertOfEndpoints e) : ℝ) /
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
      (advancePanel x (mainPanelCertOfEndpoints e) : ℝ) / (Spike.gridScale : ℝ) := by
    simp [advancePanel, ceilGridProduct, mainPanelCertOfEndpoints,
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
theorem main_eight_panel_grid_fold_of_endpoint
    (f : ℝ → ℝ) (e : ℕ → PanelEndpoints) (x : ℕ → ℕ)
    (hstart : f 0 ≤ (x 0 : ℝ) / (Spike.gridScale : ℝ))
    (hnext : ∀ j : ℕ, j < 8 → x (j + 1) = advancePanel (x j)
      (mainPanelCertOfEndpoints (e j)))
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
        exact main_panel_grid_advance_of_endpoint_bound (e j) (x j)
          (hend j hj8) (ih (by omega))
  have hlast := hbound 8 le_rfl
  norm_num at hlast ⊢
  exact hlast

/-- At time `0` the heat average is the completed OLD mean. -/
theorem modelTraceHeatAverage_zero_eq (q : ℤ) (M : ABKModel 2) (m : ℤ) :
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

theorem frame_ceil_step (frameUpper x : ℕ) {t : ℝ}
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

/-- One insertion of the chronology, in endpoint form: from the grid bound on the completed
OLD mean at label `m` on cube `q`, and the eight endpoint recurrences of the heat average, the
completed mean at label `m + 1` obeys the `advanceInsertion` step. -/
theorem main_insertion_step_of_endpoint_bounds
    (M : ABKModel 2) (hgamma : M.gamma ≤ ASDExplicitGamma.gammaZero) (m q : ℤ)
    (cert : InsertionCert)
    (hframe : insertionFrameRecurrenceFields cert.frameLower cert.frameUpper)
    (e : ℕ → PanelEndpoints)
    (hcert : cert.panels = (List.range 8).map
      (fun j => mainPanelCertOfEndpoints (e j)))
    (x0 : ℕ)
    (hOld : (∫ ω, cutoffTraceDefect M m q ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (x0 : ℝ) / (Spike.gridScale : ℝ))
    (hend : ∀ j : ℕ, j < 8 → modelTraceHeatAverage q M m (((j + 1 : ℕ) : ℝ) / 8) ≤
      (e j).rhoUpper / (Spike.gridScale : ℝ) * modelTraceHeatAverage q M m ((j : ℝ) / 8) +
        (e j).offsetUpper / (Spike.gridScale : ℝ)) :
    (∫ ω, cutoffTraceDefect M (m + 1) q ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (advanceInsertion x0 cert : ℝ) / (Spike.gridScale : ℝ) := by
  obtain ⟨x, hx0, hnext⟩ : ∃ x : ℕ → ℕ, x 0 = x0 ∧ ∀ j : ℕ, j < 8 →
      x (j + 1) = advancePanel (x j) (mainPanelCertOfEndpoints (e j)) :=
    ⟨fun j => Nat.rec x0
      (fun i v => advancePanel v (mainPanelCertOfEndpoints (e i))) j,
      rfl, fun j _ => rfl⟩
  have hstart : modelTraceHeatAverage q M m 0 ≤ ((x 0 : ℕ) : ℝ) / (Spike.gridScale : ℝ) := by
    rw [modelTraceHeatAverage_zero_eq, hx0]
    exact hOld
  have hpanels := main_eight_panel_grid_fold_of_endpoint
    (modelTraceHeatAverage q M m) e x hstart hnext hend
  -- frame restoration
  have hratio := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity M m 1 (by norm_num)
  have hratio' :
      1 ≤ (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ) ∧
      (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ) ≤
        Real.rpow 3 (2 * M.gamma) := by
    simpa using hratio
  have hexponent : 2 * M.gamma ≤ (mainReturnFrameExponent : ℚ) := by
    have hframeExponent : (mainReturnFrameExponent : ℝ) =
        2 * ASDExplicitGamma.gammaZero := by
      norm_num [mainReturnFrameExponent, ASDExplicitGamma.gammaZero]
    rw [hframeExponent]
    nlinarith [hgamma]
  have hpower := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexponent
  have hframeUpper : Real.rpow 3 (2 * M.gamma) ≤
      (cert.frameUpper : ℝ) / (Spike.gridScale : ℝ) := hpower.trans hframe.2
  have hret := main_completed_endpoint_return_of_ratio M m q
    ((cert.frameUpper : ℝ) / (Spike.gridScale : ℝ)) hratio'.1
    (hratio'.2.trans hframeUpper)
  have hstep := frame_ceil_step cert.frameUpper (x 8) hpanels
  have hfold : cert.panels.foldl advancePanel x0 = x 8 := by
    have hfold := main_panel_grid_recurrence_eq_range_fold e x hnext
    rw [hx0] at hfold
    rw [hcert, List.foldl_map]
    exact hfold.symm
  refine hret.trans ?_
  simp only [advanceInsertion, hfold]
  exact hstep

end ASDExplicitGamma.Main

end
