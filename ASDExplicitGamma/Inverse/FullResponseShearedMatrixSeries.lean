module

public import ASDExplicitGamma.Inverse.FullResponseShearedMatrixBudget
public import ASDExplicitGamma.Inverse.FullResponseShearedLayerConcentration
public import ASDExplicitGamma.Inverse.AssemblyMatrixSeries

/-! Complete actual added-stream matrix errors at the fixed full-response entrance, before height selection. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal Matrix.Norms.Elementwise
noncomputable section

/-- Actual sheared full-matrix deviation, with the physical added-stream sign. -/
def fullResponseTraceMatrixDeviation (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
    (assemblyShearedCenteredLayerMatrix M Q H i (rootTau .full) N weights ω)‖

/-- Complete positive matrix summand on a deterministic height and layer. -/
def fullResponseTraceMatrixTerm (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (N : ℤ) (weights : ℤ → ℝ) (hk : ℕ × ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (rootEdelta .full)*rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1)*
    fullResponseTraceMatrixDeviation M Q (H0+hk.1) (hk.2+1) N weights ω

theorem full_response_trace_matrix_deviation_measurable (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (N : ℤ) (weights : ℤ → ℝ) :
    Measurable (fullResponseTraceMatrixDeviation M Q H i N weights) := by
  let T := Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ)
  let L : FullBlockMat 2 →ₗ[ℝ]
      (EuclideanSpace ℝ (BlockCoord 2) →L[ℝ] EuclideanSpace ℝ (BlockCoord 2)) :=
    { toFun := T
      map_add' := fun A B => map_add T A B
      map_smul' := fun r A => map_smul T r A }
  apply L.continuous_of_finiteDimensional.norm.measurable.comp
  apply Measurable.of_eval_matrix
  intro a b
  simp only [assemblyShearedCenteredLayerMatrix,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,Matrix.mul_apply,Matrix.sub_apply,Matrix.transpose_apply]
  apply Finset.measurable_sum
  intro U _
  have hR := assembly_physical_shear_measurable M (U.scale+40) U.scale N
    (((U.index 0:ℝ)-1/2)*(3:ℝ)^U.scale) (((U.index 1:ℝ)-1/2)*(3:ℝ)^U.scale) weights
  have hY := clipped_cell_matrix_measurable M (U.scale+40) U (rootTau .full)
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro v _
  apply Measurable.mul
  · apply Finset.measurable_sum
    intro u _
    exact ((measurable_pi_apply a).comp ((measurable_pi_apply u).comp hR)).mul
      (((measurable_pi_apply v).comp ((measurable_pi_apply u).comp hY)).sub_const _)
  · exact (measurable_pi_apply b).comp ((measurable_pi_apply v).comp hR)

/-- Each full-response sheared term retains the source's complete wave bracket. -/
theorem full_response_trace_matrix_term_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (H0 : ℕ) (hH0 : 377 ≤ H0)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342 → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (Q.scale-342) N,
      0 ≤ weights n ∧ weights n ≤ 1) (hk : ℕ × ℕ) :
    Measurable (fullResponseTraceMatrixTerm M Q H0 N
      (sourceBandWeights (Q.scale-342) weights) hk) ∧
      eLpNorm (fullResponseTraceMatrixTerm M Q H0 N
        (sourceBandWeights (Q.scale-342) weights) hk)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal (fullResponseTraceMatrixBudgetTerm M.gamma p ((N-Q.scale+1:ℤ):ℝ) H0 hk) := by
  let a := sourceBandWeights (Q.scale-342) weights
  let w := (rootEdelta .full)*rootAssemblyClock M.gamma (H0+hk.1) (hk.2+1)
  let x := (localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)
  let D := ((N-Q.scale+1:ℤ):ℝ)
  have hw0 : 0 ≤ w := mul_nonneg ((Real.exp_pos _).le : 0 ≤ rootEdelta .full)
    (root_assembly_clock_pos _ _ _).le
  have hm := (full_response_trace_matrix_deviation_measurable M Q (H0+hk.1) (hk.2+1) N a).const_mul w
  refine ⟨hm, ?_⟩
  have he : fullResponseTraceMatrixTerm M Q H0 N a hk =
      w • fullResponseTraceMatrixDeviation M Q (H0+hk.1) (hk.2+1) N a := rfl
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal hw0]
  have hb := full_response_sheared_centered_layer_Lp M h hM Q p hp
    (H0+hk.1) (hk.2+1) (by omega) (by omega) N hN (rootTau .full)
    (by norm_num [rootTau]) a
    (source_band_weights_bounds _ _ N weights hw) hpast
  apply (mul_le_mul_right hb (ENNReal.ofReal w)).trans
  rw [← ENNReal.ofReal_mul hw0]
  apply ENNReal.ofReal_le_ofReal
  have h38 : 38 ≤ H0 := by omega
  have hx : layerRelativeOffset (H0+hk.1) (hk.2+1) =
      localizationResetAbscissa (H0-38) hk.1 hk.2 := by
    unfold layerRelativeOffset layerProfile localizationResetAbscissa localizationProfileDepth
    omega
  have hgap : ((N-layerOldCutoff Q.scale (H0+hk.1) (hk.2+1):ℤ):ℝ)=D+x := by
    rw [layer_old_cutoff_eq_source_offset Q.scale (H0+hk.1) (hk.2+1) (by omega) (by omega),hx]
    dsimp only [D,x]
    push_cast
    ring
  have hdepth : layerDepth (H0+hk.1) (hk.2+1) =
      hk.2+1+whitneyProfile (H0+hk.1) (hk.2+1) := by
    unfold layerDepth layerProfile whitneyProfile
    omega
  have hf := root_matrix_depth_factor H0 hk.1 hk.2 h38
  have hv : Real.sqrt (bankLayerWeight hk.2) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    simpa only [layerWeight_hasSum.tsum_eq] using
      layerWeight_hasSum.summable.le_tsum hk.2 (fun _ _ => bankLayerWeight_nonneg _)
  have hg0 : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hD0 : 0 ≤ D := by dsimp only [D]; exact_mod_cast (by omega : 0 ≤ N-Q.scale+1)
  have hx0 : 0 ≤ x := Nat.cast_nonneg _
  have hτ0 : 0 ≤ (rootTau .full) := by norm_num [rootTau]
  have hs0 := ((Real.exp_pos _).le : 0 ≤ rootEdelta .full)
  have hc0 : 0 ≤ (rootEdelta .full)*256*Real.sqrt p*rootResponseEnvelope (rootTau .full)*
      ((3:ℝ)^(2*M.gamma*x)*(3:ℝ)^(-(x+1)))*
      (2+80*(p+2)*(M.gamma*(D+x)*(3:ℝ)^(2*M.gamma*(D+x)))) := by
    unfold rootResponseEnvelope
    positivity
  have hfactor : w*(256*(1+(rootTau .full)+Real.sqrt ((rootTau .full)*((rootTau .full)+2)))*
      Real.sqrt p*Real.sqrt (bankLayerWeight (hk.2+1-1))*
      (1/3:ℝ)^layerDepth (H0+hk.1) (hk.2+1)*(3:ℝ)^40*
      (2+80*(p+2)*(M.gamma*((N-layerOldCutoff Q.scale (H0+hk.1) (hk.2+1):ℤ):ℝ)*
        (3:ℝ)^(2*M.gamma*((N-layerOldCutoff Q.scale (H0+hk.1) (hk.2+1):ℤ):ℝ))))) =
      fullResponseTraceMatrixBudgetTerm M.gamma p D H0 hk*Real.sqrt (bankLayerWeight hk.2) := by
    rw [hgap,hdepth,Nat.add_sub_cancel]
    dsimp only [w]
    rw [assembly_clock_eq_reset _ _ h38]
    have halg := assembly_trace_matrix_envelope_factor M.gamma p D x
      ((rootEdelta .full)*256*Real.sqrt p*rootResponseEnvelope (rootTau .full))
    dsimp only [fullResponseTraceMatrixBudgetTerm]
    rw [← halg]
    dsimp only [rootResponseEnvelope,x] at *
    calc
      _ = ((rootEdelta .full)*256*Real.sqrt p*
          (1+(rootTau .full)+Real.sqrt ((rootTau .full)*((rootTau .full)+2)))*
          (3:ℝ)^(2*M.gamma*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)))*
          ((1/3:ℝ)^(hk.2+1+whitneyProfile (H0+hk.1) (hk.2+1))*(3:ℝ)^40)*
          (2+80*(p+2)*(M.gamma*(D+(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))*
            (3:ℝ)^(2*M.gamma*(D+(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ)))))*
          Real.sqrt (bankLayerWeight hk.2) := by ring
      _ = _ := by rw [hf]; ring
  rw [hfactor]
  apply mul_le_of_le_one_right _ hv
  dsimp only [fullResponseTraceMatrixBudgetTerm]
  rw [← assembly_trace_matrix_envelope_factor]
  exact hc0

/-- Complete actual sheared-matrix error series, summed before selection.
Its closed budget retains both the depth and first depth moment terms. -/
theorem full_response_trace_matrix_series_Lp (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (H0 : ℕ) (hH0 : 377 ≤ H0)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342 → nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc (Q.scale-342) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    let F := fullResponseTraceMatrixTerm M Q H0 N
      (sourceBandWeights (Q.scale-342) weights)
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, Summable (fun hk => ‖F hk ω‖)) ∧
      eLpNorm (fun ω => ∑' hk, F hk ω) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (fullResponseTraceMatrixBudget M.gamma p ((N-Q.scale+1:ℤ):ℝ) H0) := by
  have hD : 0 ≤ ((N-Q.scale+1:ℤ):ℝ) := by exact_mod_cast (by omega : 0 ≤ N-Q.scale+1)
  exact countable_density_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure
    (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
    (fullResponseTraceMatrixTerm M Q H0 N
      (sourceBandWeights (Q.scale-342) weights))
    (fun hk => (full_response_trace_matrix_term_Lp M h hM Q p hp H0 hH0 hpast N hN weights hw hk).1)
    (fullResponseTraceMatrixBudgetTerm M.gamma p ((N-Q.scale+1:ℤ):ℝ) H0)
    (full_response_trace_matrix_budget_term_nonneg M.gamma p _ M.shellPrefix.gamma_pos.le
      (by linarith only [hp]) hD H0)
    _ (full_response_trace_matrix_budget_hasSum M.gamma p _ hγ H0)
    (fun hk => (full_response_trace_matrix_term_Lp M h hM Q p hp H0 hH0 hpast N hN weights hw hk).2)

end
end ASDExplicitGamma.Inverse
