module

public import ASDExplicitGamma.Inverse.FullResponseTraceRootAssembly
public import ASDExplicitGamma.Inverse.FullResponseShearedMatrixSeries

/-! Exact full-row scalar mean-plus-error assembly on every deterministic layer. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Source full-row leading mean coefficient, before selection or numerics. -/
def fullResponseTraceBaseline : ℝ :=
  (29/25:ℝ)+3*(planarGradientCharge 40+1)*fullResponseTraceC0*
    densityMomentBudget (rootQ .full) 2 1232

/-- Literal source scalar layer with exact identity volume and full sheared
matrix error. The active root fourth moment retains sqrt(v_k). -/
def fullResponseTraceScalarLayer (M : ABKModel 2) (Q : TriadicCube 2)
    (hk : ℕ × ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let H := 377+hk.1
  let i := hk.2
  let a := sourceBandWeights (Q.scale-342) weights
  let Y := fun m e => resetDensityExcess M Q 377 (rootTau .full) (waveGateEta .full)
    (rootQ .full) 1232 m hk e ω
  let W := fullResponseLayerWaveFourth M Q 377 hk (Q.scale-342) N weights ω
  rootEdelta .full*rootAssemblyClock M.gamma H (i+1)*
    (fullResponseTraceBaseline*bankLayerWeight i+
      (29/25:ℝ)*(assemblyLayerMeanSquare M Q H (i+1) N a ω/2)+
      3*(planarGradientCharge 40+1)*fullResponseTraceC1*
        Real.sqrt (densityMomentBudget (rootQ .full) 4 1232)*Real.sqrt (bankLayerWeight i)*W+
      fullResponseTraceMatrixDeviation M Q H (i+1) N a ω+
      (planarGradientCharge 40+1)*
        (fullResponseTraceC0*(∑ e : Fin 3, Y 2 e)+
          fullResponseTraceC1*W*(∑ e : Fin 3, Real.sqrt (Y 4 e))))

/-- The full-row analogue of `TraceLayerBound`: exact old means plus all
actual positive density and centered-matrix errors, with no wave loss. -/
theorem full_response_trace_layer_le_scalar
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-342, nativeInductionState M h n)
    (hk : ℕ × ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    let H := 377+hk.1
    let i := hk.2
    let a := sourceBandWeights (Q.scale-342) weights
    rootEdelta .full*rootAssemblyClock M.gamma H (i+1)*
      fullResponseShearedLayerTrace M Q H (i+1) N a ω+
      (rootEdelta .full*(planarGradientCharge 40+1))*
        (rootAssemblyClock M.gamma H (i+1)*
          fullResponseActiveLayerDensity M Q H (i+1) N weights ω) ≤
      fullResponseTraceScalarLayer M Q hk N weights ω := by
  dsimp only
  have hi := full_response_sheared_layer_mean_bound M h hg Q (377+hk.1)
    (by omega) hpast hk.2 N (sourceBandWeights (Q.scale-342) weights) ω
  have ha := full_response_active_layer_density_le M Q hk (rootQ .full) 1232 N weights ω
  have hE : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  have hc := (root_assembly_clock_pos M.gamma (377+hk.1) (hk.2+1)).le
  have hS : 0 ≤ planarGradientCharge 40+1 := by unfold planarGradientCharge; positivity
  have hhi := mul_le_mul_of_nonneg_left hi (mul_nonneg hE hc)
  have hha := mul_le_mul_of_nonneg_left ha (mul_nonneg (mul_nonneg hE hS) hc)
  dsimp only [fullResponseTraceScalarLayer,fullResponseTraceBaseline,
    fullResponseTraceMatrixDeviation]
  convert add_le_add hhi hha using 1 <;> ring

end
end ASDExplicitGamma.Inverse
