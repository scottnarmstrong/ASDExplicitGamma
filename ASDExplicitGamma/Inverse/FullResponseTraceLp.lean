module

public import ASDExplicitGamma.Inverse.FullResponseComponentBudgets
public import ASDExplicitGamma.Inverse.AssemblyTraceMeasurable

/-! Complete actual full-response Lp assembly before certified endpoint comparisons. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- Finite Minkowski with separate exact extended component caps. -/
theorem full_response_finite_component_Lp {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (p : ℝ≥0∞) (hp : 1 ≤ p) (f : I → Ω → ℝ) (B : I → ℝ≥0∞)
    (hf : ∀ i, eLpNorm (f i) p μ ≤ B i) :
    eLpNorm (fun ω => ∑ i, f i ω) p μ ≤ ∑ i, B i := by
  have he : (fun ω => ∑ i, f i ω) = ∑ i, f i := by funext ω; simp only [Finset.sum_apply]
  rw [he]
  exact (eLpNorm_sum_le hp).trans (Finset.sum_le_sum (fun i _ => hf i))

/-- The actual normalized full trace has the complete source selected-wave,
density and sheared-matrix budget. Every probability, geometry, convergence,
and moment estimate is discharged internally; no bank conclusion is a premise. -/
theorem full_response_trace_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    eLpNorm (fun ω => rootTraceObservable M Q (Q.scale-342) N (Q.scale-1) weights ω/4)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        fullResponseTraceExtendedBudget M.gamma p ((N:ℝ)-(Q.scale:ℝ)+1) := by
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith only [hp])
  have hmodel := full_response_trace_ae_le_component_envelope M h hM hg Q hpast N hN weights hw
  have hmeas := (root_trace_observable_measurable M Q (Q.scale-342) N (Q.scale-1) weights).div_const 4
  have hmono : eLpNorm (fun ω => rootTraceObservable M Q (Q.scale-342) N (Q.scale-1) weights ω/4)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      eLpNorm (fullResponseTraceComponentEnvelope M Q N weights) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply eLpNorm_mono_ae_real hmeas.aestronglyMeasurable
    filter_upwards [hmodel] with ω hω
    have htrace : 0 ≤ rootTraceObservable M Q (Q.scale-342) N (Q.scale-1) weights ω/4 :=
      div_nonneg (root_trace_observable_nonneg M Q (Q.scale-342) N (Q.scale-1)
        (by omega) weights ω) (by norm_num)
    have henv : 0 ≤ fullResponseTraceComponentEnvelope M Q N weights ω := by
      unfold fullResponseTraceComponentEnvelope
      exact add_nonneg
        (Finset.sum_nonneg (fun a _ => tsum_nonneg
          (fun k => full_response_trace_leading_nonneg M Q N weights a k ω)))
        (Finset.sum_nonneg (fun b _ => tsum_nonneg
          (fun hk => full_response_trace_error_nonneg M Q N hN weights b hk ω)))
    rw [Real.norm_eq_abs,abs_of_nonneg htrace]
    exact (ENNReal.ofReal_le_ofReal_iff henv).mp hω
  have hlead := full_response_finite_component_Lp (Cutoff.cutoffSampleLaw M).toMeasure
    (ENNReal.ofReal p) hp1
    (fun a ω => ∑' k, fullResponseTraceLeading M Q N weights a k ω)
    (fun a => ENNReal.ofReal (fullResponseTraceLeadingBudget M.gamma p ((N:ℝ)-(Q.scale:ℝ)+1) a))
    (fun a => full_response_trace_leading_component_Lp M h hM hg Q hpast N hN weights hw p hp hp256 a)
  have herr := full_response_finite_component_Lp (Cutoff.cutoffSampleLaw M).toMeasure
    (ENNReal.ofReal p) hp1
    (fun b ω => ∑' hk, fullResponseTraceError M Q N weights b hk ω)
    (fun b => ENNReal.ofReal (fullResponseTraceErrorBudget M.gamma p ((N:ℝ)-(Q.scale:ℝ)+1) b))
    (fun b => full_response_trace_error_component_Lp M h hM hg Q hpast N hN weights hw p hp hp256 b)
  apply hmono.trans
  exact (eLpNorm_add_le hp1).trans (add_le_add hlead herr)

end
end ASDExplicitGamma.Inverse
