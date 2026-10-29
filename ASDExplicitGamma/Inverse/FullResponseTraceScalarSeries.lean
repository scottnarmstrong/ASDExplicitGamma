module

public import ASDExplicitGamma.Inverse.FullResponseTraceLayerBound

/-! The actual full-response trace majorant is controlled by scalar positive layers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Regroup the complete positive identity and active sums, removing only
the empty zeroth Whitney layer, as in the `TraceScalarSeries` assembly. -/
theorem full_response_trace_majorant_eq_grouped (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    fullResponseTraceLayerMajorant M Q H N weights ω =
      ∑' i : ℕ, ENNReal.ofReal
        (rootEdelta .full*rootAssemblyClock M.gamma H (i+1)*
          fullResponseShearedLayerTrace M Q H (i+1) N
            (sourceBandWeights (Q.scale-342) weights) ω+
          (rootEdelta .full*(planarGradientCharge 40+1))*
            (rootAssemblyClock M.gamma H (i+1)*
              fullResponseActiveLayerDensity M Q H (i+1) N weights ω)) := by
  let I := fun n => rootAssemblyClock M.gamma H n*
    fullResponseShearedLayerTrace M Q H n N (sourceBandWeights (Q.scale-342) weights) ω
  let A := fun n => rootAssemblyClock M.gamma H n*
    fullResponseActiveLayerDensity M Q H n N weights ω
  let E := rootEdelta .full
  let C := rootEdelta .full*(planarGradientCharge 40+1)
  have hI0 : I 0=0 := by
    simp only [I,fullResponseShearedLayerTrace,root_whitney_layer_zero,Finset.sum_empty,mul_zero]
  have hA0 : A 0=0 := by
    simp only [A,fullResponseActiveLayerDensity,root_whitney_layer_zero,Finset.sum_empty,
      Finset.sum_const_zero,mul_zero]
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hC : 0 ≤ C := by dsimp only [C]; unfold rootEdelta planarGradientCharge; positivity
  have hI (n : ℕ) : 0 ≤ I n := mul_nonneg (root_assembly_clock_pos _ _ _).le
    (full_response_sheared_layer_trace_nonneg M Q H n N _ ω)
  have hA (n : ℕ) : 0 ≤ A n := mul_nonneg (root_assembly_clock_pos _ _ _).le
    (full_response_active_layer_density_nonneg M Q H n N weights ω)
  change ENNReal.ofReal E*(∑' n, ENNReal.ofReal (I n))+
    ENNReal.ofReal C*(∑' n, ENNReal.ofReal (A n)) = _
  rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_left,← ENNReal.tsum_add,
    tsum_eq_zero_add' ENNReal.summable,hI0,hA0,ENNReal.ofReal_zero,mul_zero,mul_zero,zero_add,zero_add]
  apply tsum_congr
  intro i
  rw [← ENNReal.ofReal_mul hE,← ENNReal.ofReal_mul hC,
    ← ENNReal.ofReal_add (mul_nonneg hE (hI _)) (mul_nonneg hC (hA _))]
  congr 1
  dsimp only [E,C,I,A]
  ring

/-- The full actual positive trace majorant is bounded by the scalar
mean-plus-error series at any height above the fixed full entrance. -/
theorem full_response_trace_majorant_le_scalar_series
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (H : ℕ) (hH : 377 ≤ H)
    (hpast : ∀ n ≤ Q.scale-342, nativeInductionState M h n)
    (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    fullResponseTraceLayerMajorant M Q H N weights ω ≤
      ∑' i : ℕ, ENNReal.ofReal (fullResponseTraceScalarLayer M Q (H-377,i) N weights ω) := by
  rw [full_response_trace_majorant_eq_grouped]
  apply ENNReal.tsum_le_tsum
  intro i
  apply ENNReal.ofReal_le_ofReal
  simpa only [Nat.add_sub_of_le hH] using
    full_response_trace_layer_le_scalar M h hg Q hpast (H-377,i) N weights ω

end
end ASDExplicitGamma.Inverse
