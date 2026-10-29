module

public import ASDExplicitGamma.Inverse.FullResponseTraceComponents
public import ASDExplicitGamma.Inverse.RootLayerProfile
public import ASDExplicitGamma.Inverse.FixedSelectedHeight

/-! Exact baseline layer sum and its full-row selected-height moment. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- The actual leading baseline retains exactly A(2gamma) and the selected clock. -/
theorem full_response_baseline_hasSum (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    HasSum (fun k => fullResponseTraceLeading M Q N weights 0 k ω)
      ((rootEdelta .full*fullResponseTraceBaseline*rootLayerSum (2*M.gamma))*
        (3:ℝ)^(2*M.gamma*((rootSelectedHeight M Q .full ω:ℝ)-38))) := by
  have hH : rootH0 .full ≤ rootSelectedHeight M Q .full ω :=
    q3_stopped_height_ge M Q 377 (rootTau .full) (waveGateEta (rootWaveTuple .full)) ω
  have hh := (root_clocked_layer_weights_hasSum M.gamma hg .full
    (rootSelectedHeight M Q .full ω) hH).mul_left (rootEdelta .full*fullResponseTraceBaseline)
  convert hh using 1
  · funext k
    simp only [fullResponseTraceLeading,Matrix.cons_val_zero]
    have hh := assembly_clock_eq_reset M.gamma 377 (by norm_num)
      (rootSelectedHeight M Q .full ω-377,k)
    simp only [Nat.add_sub_of_le (show 377 ≤ rootSelectedHeight M Q .full ω from hH)] at hh
    rw [hh]
    simp only [rootH0]
    ring
  · ring

/-- The literal selected-clock baseline moment at the fixed full entrance. -/
theorem full_response_baseline_series_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (weights : ℤ → ℝ) (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    eLpNorm (fun ω => ∑' k, fullResponseTraceLeading M Q N weights 0 k ω)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
        ((rootEdelta .full*fullResponseTraceBaseline*rootLayerSum (2*M.gamma))*
          selectedJp M.gamma p 377) := by
  let H := rootSelectedHeight M Q .full
  let clock := fun ω : Cutoff.CutoffSample 2 => (3:ℝ)^(2*M.gamma*((H ω:ℝ)-38))
  let C := rootEdelta .full*fullResponseTraceBaseline*rootLayerSum (2*M.gamma)
  have hC : 0 ≤ C := by
    have hE : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
    have hB := full_response_trace_baseline_nonneg
    have hA : 0 ≤ rootLayerSum (2*M.gamma) :=
      tsum_nonneg (fun k => mul_nonneg (bankLayerWeight_nonneg k) (by positivity))
    exact mul_nonneg (mul_nonneg hE hB) hA
  have he : (fun ω => ∑' k, fullResponseTraceLeading M Q N weights 0 k ω) = C • clock := by
    funext ω
    exact (full_response_baseline_hasSum M hg Q N weights ω).tsum_eq
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal hC]
  obtain ⟨hq0,hq,hraw⟩ := root_row_density_inputs .full
  have hc := q3_selected_clock_Lp M h hM hg Q 377 (by norm_num)
    (rootTau .full) (by norm_num [rootTau]) .full (rootQ .full) hq0 hq hraw
    (by intro k hk; apply hpast k; omega) p (by linarith only [hp]) hp256
  have hcast : eLpNorm (selectedHeightClock M.gamma H) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure =
        eLpNorm clock (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure := by
    change eLpNorm (ENNReal.ofReal ∘ clock) _ _ = _
    exact eLpNorm_ofReal clock (Filter.Eventually.of_forall (fun _ => by dsimp only [clock]; positivity))
  change eLpNorm (selectedHeightClock M.gamma H) _ _ ≤ _ at hc
  rw [hcast] at hc
  change ENNReal.ofReal C*eLpNorm clock (ENNReal.ofReal p) _ ≤
    ENNReal.ofReal (C*selectedJp M.gamma p 377)
  rw [ENNReal.ofReal_mul hC]
  exact mul_le_mul_of_nonneg_left hc bot_le

end
end ASDExplicitGamma.Inverse
