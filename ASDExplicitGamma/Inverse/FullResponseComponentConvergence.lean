module

public import ASDExplicitGamma.Inverse.FullResponseBaselineSeries
public import ASDExplicitGamma.Inverse.StoppedPastDiameterFinite

/-! Convergence of every actual trace component and the model-level root envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- All convergence inputs in the pathwise component grouping are proved
from the actual source moment suppliers. -/
theorem full_response_components_ae_summable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (∀ a, Summable (fun k => fullResponseTraceLeading M Q N weights a k ω)) ∧
      (∀ b, Summable (fun hk => fullResponseTraceError M Q N weights b hk ω)) := by
  have hprotected : ∀ n ≤ Q.scale-342, nativeInductionState M h n := by
    intro n hn
    apply hpast n
    omega
  have hi := full_response_identity_wave_series_Lp M h hM hg Q hpast N hN weights hw p hp hp256
  have ha := full_response_active_wave_series_Lp M h hM hg Q hpast N hN weights hw p hp hp256
  have hm := full_response_trace_matrix_series_Lp M h hM hg Q p hp 377 (by norm_num)
    hprotected N hN weights hw
  have hd := full_response_density_series_Lp M h hM hg Q hpast p hp hp256
  have hc0 := full_response_correlated_series_Lp M h hM hg Q hpast N hN weights hw 0 p hp hp256
  have hc1 := full_response_correlated_series_Lp M h hM hg Q hpast N hN weights hw 1 p hp hp256
  filter_upwards [hi.1,ha.1,hm.1,hd.1,hc0.1,hc1.1] with ω hiω haω hmω hdω hc0ω hc1ω
  constructor
  · intro a
    fin_cases a
    · exact (full_response_baseline_hasSum M hg Q N weights ω).summable
    · simpa [fullResponseTraceLeading] using
        (Summable.of_norm hiω).mul_left (rootEdelta .full*(29/25:ℝ))
    · simpa [fullResponseTraceLeading] using
        (Summable.of_norm haω).mul_left
          (rootEdelta .full*3*(planarGradientCharge 40+1)*fullResponseTraceC1*
            Real.sqrt (densityMomentBudget (rootQ .full) 4 1232))
  · intro b
    fin_cases b
    · simpa [fullResponseTraceError] using Summable.of_norm hmω
    · simpa [fullResponseTraceError] using
        (Summable.of_norm hdω).mul_left (rootEdelta .full*fullResponseTraceC0)
    · simpa [fullResponseTraceError] using
        (Summable.of_norm hc0ω).mul_left
          ((rootEdelta .full*fullResponseTraceC1*M.gamma*
            (3:ℝ)^(2*M.gamma*((N:ℝ)-(Q.scale:ℝ)+1))/2)*((N:ℝ)-(Q.scale:ℝ)+1))
    · simpa [fullResponseTraceError] using
        (Summable.of_norm hc1ω).mul_left
          (rootEdelta .full*fullResponseTraceC1*M.gamma*
            (3:ℝ)^(2*M.gamma*((N:ℝ)-(Q.scale:ℝ)+1))/2)

/-- The actual model full trace is bounded by the complete component
envelope a.e.; neither geometry nor convergence is assumed in the interface. -/
theorem full_response_trace_ae_le_component_envelope
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal (rootTraceObservable M Q (Q.scale-342) N (Q.scale-1) weights ω/4) ≤
        ENNReal.ofReal (fullResponseTraceComponentEnvelope M Q N weights ω) := by
  obtain ⟨hq0,hq,hraw⟩ := root_row_density_inputs .full
  have hτ : 0 < rootTau .full := by norm_num [rootTau]
  have hprotected : ∀ n ≤ Q.scale-(377:ℤ)+40, nativeInductionState M h n := by
    intro n hn
    apply hpast n
    omega
  have hgood := q3_stopped_height_ae_good M h hM hg Q 377 (by norm_num)
    (rootTau .full) hτ .full (rootQ .full) hq0 hq hraw hprotected
  have hfinite := q3_past_diameter_ae_ne_top M h hM hg (Q.scale-377)
    (rootTau .full) hτ .full (rootQ .full) hq0 hq hraw
    (by intro n hn; apply hpast n; omega)
  have hsum := full_response_components_ae_summable M h hM hg Q hpast N hN weights hw
    64 (by norm_num) (by norm_num)
  filter_upwards [hgood,hfinite,hsum] with ω hgω hfω hsω
  have hH : 377 ≤ rootSelectedHeight M Q .full ω :=
    q3_stopped_height_ge M Q 377 (rootTau .full) (waveGateEta (rootWaveTuple .full)) ω
  exact full_response_trace_le_component_envelope M h hg Q
    (by intro n hn; apply hpast n; omega) N hN weights hw ω hgω
    (fun j hj z => hfω j (by omega) z) hsω.1 hsω.2

end
end ASDExplicitGamma.Inverse
