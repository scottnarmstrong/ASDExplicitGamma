module

public import ASDExplicitGamma.Inverse.FullResponseSeriesPositivity
public import ASDExplicitGamma.Inverse.FullResponsePositiveSeriesSelection

/-! Actual source components and the complete positive full-response trace envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal
noncomputable section

/-- The three selected leading components, before their countable layer sums. -/
def fullResponseTraceLeading (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (a : Fin 3) (k : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ![rootEdelta .full*fullResponseTraceBaseline*
      rootAssemblyClock M.gamma (rootSelectedHeight M Q .full ω) (k+1)*bankLayerWeight k,
    (rootEdelta .full*(29/25:ℝ))*fullResponseIdentityWaveTerm M Q N weights k ω,
    (rootEdelta .full*3*(planarGradientCharge 40+1)*fullResponseTraceC1*
      Real.sqrt (densityMomentBudget (rootQ .full) 4 1232))*
        fullResponseActiveWaveTerm M Q N weights k ω] a

/-- The four positive error components are summed before height selection. -/
def fullResponseTraceError (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (b : Fin 4) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let D := (N:ℝ)-(Q.scale:ℝ)+1
  let c := rootEdelta .full*fullResponseTraceC1*M.gamma*(3:ℝ)^(2*M.gamma*D)/2
  ![fullResponseTraceMatrixTerm M Q 377 N (sourceBandWeights (Q.scale-342) weights) hk ω,
    (rootEdelta .full*fullResponseTraceC0)*fullResponseDensityTerm M Q hk ω,
    (c*D)*fullResponseCorrelatedTerm M Q N weights 0 hk ω,
    c*fullResponseCorrelatedTerm M Q N weights 1 hk ω] b

/-- Complete positive actual envelope, with selected leading terms and all
four deterministic height/layer error series. -/
def fullResponseTraceComponentEnvelope (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (∑ a : Fin 3, ∑' k, fullResponseTraceLeading M Q N weights a k ω)+
    ∑ b : Fin 4, ∑' hk, fullResponseTraceError M Q N weights b hk ω

theorem full_response_trace_leading_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (a : Fin 3) (k : ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ fullResponseTraceLeading M Q N weights a k ω := by
  have hE : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  have hB := full_response_trace_baseline_nonneg
  have hclock := (root_assembly_clock_pos M.gamma (rootSelectedHeight M Q .full ω) (k+1)).le
  have hv := bankLayerWeight_nonneg k
  have hI := full_response_identity_wave_term_nonneg M Q N weights k ω
  have hA := full_response_active_wave_term_nonneg M Q N weights k ω
  have hS : 0 ≤ planarGradientCharge 40+1 := by unfold planarGradientCharge; positivity
  have hc1 : 0 ≤ fullResponseTraceC1 := by unfold fullResponseTraceC1 rootTau; positivity
  fin_cases a <;> simp [fullResponseTraceLeading] <;> positivity

theorem full_response_trace_error_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ) (b : Fin 4)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ fullResponseTraceError M Q N weights b hk ω := by
  have hE : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  have hc0 : 0 ≤ fullResponseTraceC0 := by unfold fullResponseTraceC0 rootTau; positivity
  have hc1 : 0 ≤ fullResponseTraceC1 := by unfold fullResponseTraceC1 rootTau; positivity
  have hγ := M.shellPrefix.gamma_pos.le
  have hD : (0:ℝ) ≤ (N:ℝ)-(Q.scale:ℝ)+1 := by exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  have hM := full_response_matrix_term_nonneg M Q N (sourceBandWeights (Q.scale-342) weights) hk ω
  have hD2 := full_response_density_term_nonneg M Q hk ω
  have hC0 := full_response_correlated_term_nonneg M Q N hN weights 0 hk ω
  have hC1 := full_response_correlated_term_nonneg M Q N hN weights 1 hk ω
  fin_cases b <;> simp [fullResponseTraceError] <;> positivity

/-- The actual trace is bounded by the complete positive component envelope
whenever its component series converge. Their convergence is supplied by
the source component moment theorems, separately from this pathwise grouping. -/
theorem full_response_trace_le_component_envelope
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-342, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, rootSelectedHeight M Q .full ω ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) (rootTau .full) (waveGateEta .full)) k (rootBlockStart Q k))
    (hfinite : ∀ j ≤ Q.scale-(rootSelectedHeight M Q .full ω:ℤ), ∀ z, diameterField
      (q3PlanarMarks M j (rootTau .full) (waveGateEta .full)) ω z ≠ ∞)
    (hls : ∀ a, Summable (fun k => fullResponseTraceLeading M Q N weights a k ω))
    (hes : ∀ b, Summable (fun hk => fullResponseTraceError M Q N weights b hk ω)) :
    ENNReal.ofReal (rootTraceObservable M Q (Q.scale-342) N (Q.scale-1) weights ω/4) ≤
      ENNReal.ofReal (fullResponseTraceComponentEnvelope M Q N weights ω) := by
  let H := rootSelectedHeight M Q .full ω
  have hH : 377 ≤ H := q3_stopped_height_ge M Q 377 (rootTau .full)
    (waveGateEta (rootWaveTuple .full)) ω
  have hroot := full_response_actual_trace_le_layer_majorant M Q H hH ω hgood hfinite N hN weights hw
  have hscalar := full_response_trace_majorant_le_scalar_series M h hg Q H hH hpast N weights ω
  have he (k : ℕ) : fullResponseTraceScalarLayer M Q (H-377,k) N weights ω =
      (∑ a : Fin 3, fullResponseTraceLeading M Q N weights a k ω)+
        ∑ b : Fin 4, fullResponseTraceError M Q N weights b (H-377,k) ω := by
    rw [full_response_selected_scalar_layer_eq M Q N hN weights ω k]
    simp only [fullResponseTraceLeading,fullResponseTraceError,Fin.sum_univ_succ,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
    ring
  have hs := full_response_positive_series_selection
    (fun a k => fullResponseTraceLeading M Q N weights a k ω)
    (fun b hk => fullResponseTraceError M Q N weights b hk ω) (fun k => (H-377,k))
    (fun _ _ hh => congrArg Prod.snd hh)
    (fun a k => full_response_trace_leading_nonneg M Q N weights a k ω)
    (fun b hk => full_response_trace_error_nonneg M Q N hN weights b hk ω) hls hes
  apply hroot.trans (hscalar.trans ?_)
  simp_rw [he]
  exact hs

end
end ASDExplicitGamma.Inverse
