module

public import ASDExplicitGamma.Inverse.FullResponseErrorSeries

/-! Positivity of the actual component series before height selection is removed. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
noncomputable section

/-- Actual full-response identity-wave summands are nonnegative. -/
theorem full_response_identity_wave_term_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (k : ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ fullResponseIdentityWaveTerm M Q N weights k ω := by
  unfold fullResponseIdentityWaveTerm
  apply mul_nonneg (by positivity)
  apply div_nonneg _ (by norm_num)
  unfold assemblyLayerMeanSquare
  apply Finset.sum_nonneg
  intro U _
  exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (sq_nonneg _)

/-- Actual root-fourth-moment active-wave summands are nonnegative. -/
theorem full_response_active_wave_term_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (k : ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ fullResponseActiveWaveTerm M Q N weights k ω := by
  unfold fullResponseActiveWaveTerm fullResponseLayerWaveFourth
  positivity

/-- Actual complete sheared-matrix summands are nonnegative. -/
theorem full_response_matrix_term_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ fullResponseTraceMatrixTerm M Q 377 N weights hk ω := by
  unfold fullResponseTraceMatrixTerm fullResponseTraceMatrixDeviation rootEdelta
  exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
    (root_assembly_clock_pos _ _ _).le) (norm_nonneg _)

/-- Actual complete D2 excess summands are nonnegative. -/
theorem full_response_density_term_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ fullResponseDensityTerm M Q hk ω := by
  unfold fullResponseDensityTerm resetDensityTerm2
  apply mul_nonneg
  · unfold planarGradientCharge
    positivity
  · exact Finset.sum_nonneg fun e _ => reset_density_excess_nonneg _ _ _ _ _ _ _ _ _ _ _

/-- The full-entrance reset normalization is positive even at N=l-1. -/
theorem full_response_reset_wave_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ physicalResetWave M Q N 377 a c weights hk ω := by
  have hold : physicalResetOldLabel Q 377 hk < N := by
    unfold physicalResetOldLabel localizationResetAbscissa localizationProfileDepth
    omega
  have hgap : (0:ℝ) < (N:ℝ)-(physicalResetOldLabel Q 377 hk:ℝ) := by exact_mod_cast sub_pos.mpr hold
  have hγ := M.shellPrefix.gamma_pos
  unfold physicalResetWave
  exact mul_nonneg (by positivity) (physical_missing_wave_nonneg _ _ _ _ _ _ _ _)

/-- Actual correlated D4 summands are nonnegative for both depth moments. -/
theorem full_response_correlated_term_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ) (j : Fin 2)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ fullResponseCorrelatedTerm M Q N weights j hk ω := by
  unfold fullResponseCorrelatedTerm physicalCorrelatedDensityTerm
  apply mul_nonneg
  · unfold planarGradientCharge
    positivity
  · exact Finset.sum_nonneg fun e _ => mul_nonneg
      (full_response_reset_wave_nonneg M Q N hN _ _ _ hk ω) (Real.sqrt_nonneg _)

/-- The exact full-row leading baseline coefficient is nonnegative. -/
theorem full_response_trace_baseline_nonneg : 0 ≤ fullResponseTraceBaseline := by
  have hq := (root_row_density_inputs .full).1
  have hm := density_moment_budget_nonneg (rootQ .full) hq 2 1232 (by norm_num)
  unfold fullResponseTraceBaseline fullResponseTraceC0 rootTau planarGradientCharge
  positivity

end
end ASDExplicitGamma.Inverse
