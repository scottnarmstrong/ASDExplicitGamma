module

public import ASDExplicitGamma.Inverse.AssemblyTraceLayerBound
public import ASDExplicitGamma.Inverse.AssemblyTraceRoot

/-! The complete stopped root trace is bounded by scalar positive layers. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Exact regrouping of the positive identity and active payments, with the
empty zeroth layer removed and the spatial integrals normalized by the root. -/
theorem assembly_trace_majorant_eq_grouped (M : ABKModel 2) (Q : TriadicCube 2)
    (k H : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    assemblyTraceLayerMajorant M Q k H N weights ω =
      ∑' i : ℕ, ENNReal.ofReal
        (rootAssemblySensitivity*rootAssemblyClock M.gamma H (i+1)*
          assemblyShearedLayerTrace M Q H (i+1) N
            (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω+
        (4*rootAssemblySensitivity*(1+2*Real.sqrt 3*resetAllOrderTau))*
          (rootAssemblyClock M.gamma H (i+1)*(planarGradientCharge 40+1)*
            ∑ e : Fin 3, ∫ x in rootLayerCarrier Q H (i+1),
              (layerResolutionDiameter M Q H resetAllOrderTau (waveGateEta .allOrder) (i+1) e ω x)^2*
                assemblyActiveSpatialPayment M Q k H (i+1) N weights ω x
                  ∂normalizedCubeMeasure Q)) := by
  let w := sourceBandWeights (protectedOldLabel Q.scale k) weights
  let t := fun n => assemblyShearedLayerTrace M Q H n N w ω
  let C := 4*rootAssemblySensitivity*(1+2*Real.sqrt 3*resetAllOrderTau)
  let I := fun n => rootAssemblyClock M.gamma H n*t n
  let A := fun n => rootAssemblyClock M.gamma H n*(planarGradientCharge 40+1)/
    (volume (cubeSet Q)).toReal*∑ e : Fin 3, ∫ x in rootLayerCarrier Q H n,
      (layerResolutionDiameter M Q H resetAllOrderTau (waveGateEta .allOrder) n e ω x)^2*
        assemblyActiveSpatialPayment M Q k H n N weights ω x
  have hI0 : I 0=0 := by simp only [I,t,assemblyShearedLayerTrace,root_whitney_layer_zero,Finset.sum_empty,mul_zero]
  have hA0 : A 0=0 := by simp only [A,root_layer_carrier_zero,Measure.restrict_empty,
    integral_zero_measure,Finset.sum_const_zero,mul_zero]
  have hs := root_assembly_sensitivity_pos.le
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hI (n : ℕ) : 0 ≤ I n := by
    apply mul_nonneg (root_assembly_clock_pos _ _ _).le
    apply Finset.sum_nonneg
    intro U _
    exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (assembly_sheared_clipped_trace_nonneg _ _ _ _ _ _)
  have hA (n : ℕ) : 0 ≤ A n := by
    dsimp only [A]
    apply mul_nonneg
    · apply div_nonneg _ ENNReal.toReal_nonneg
      apply mul_nonneg (root_assembly_clock_pos _ _ _).le
      unfold planarGradientCharge
      positivity
    · apply Finset.sum_nonneg
      intro e _
      apply integral_nonneg
      intro x
      apply mul_nonneg (sq_nonneg _)
      unfold assemblyActiveSpatialPayment
      exact add_nonneg (add_nonneg zero_le_one (mul_nonneg (by norm_num) (sq_nonneg _)))
        (mul_nonneg (by norm_num) (sq_nonneg _))
  change ENNReal.ofReal rootAssemblySensitivity*(∑' n, ENNReal.ofReal (I n))+
    ENNReal.ofReal C*(∑' n, ENNReal.ofReal (A n))=_
  rw [← ENNReal.tsum_mul_left,← ENNReal.tsum_mul_left,← ENNReal.tsum_add,
    tsum_eq_zero_add' ENNReal.summable,hI0,hA0,ENNReal.ofReal_zero,mul_zero,mul_zero,zero_add,zero_add]
  apply tsum_congr
  intro i
  rw [← ENNReal.ofReal_mul hs,← ENNReal.ofReal_mul hC,
    ← ENNReal.ofReal_add (mul_nonneg hs (hI _)) (mul_nonneg hC (hA _))]
  congr 1
  have hEQ : rootLayerCarrier Q H (i+1) ⊆ cubeSet Q :=
    (root_layer_carrier_subset_open Q H (i+1)).trans (openCubeSet_subset_cubeSet Q)
  simp only [assembly_normalized_layer_integral Q _ hEQ]
  dsimp only [I,A,t,w,C]
  rw [← Finset.sum_div]
  ring

/-- Every deterministic height above the entrance is controlled by the
source scalar mean-plus-positive-error series. -/
theorem assembly_trace_majorant_le_scalar_series
    (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (k H0 H : ℕ) (hH0 : heightEntrance k ≤ H0) (hH : H0 ≤ H)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*k → nativeInductionState M h n)
    (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    assemblyTraceLayerMajorant M Q k H N weights ω ≤
      ∑' i : ℕ, ENNReal.ofReal (assemblyTraceScalarLayer M Q k H0 (H-H0,i) N weights ω) := by
  rw [assembly_trace_majorant_eq_grouped]
  apply ENNReal.tsum_le_tsum
  intro i
  apply ENNReal.ofReal_le_ofReal
  simpa only [Nat.add_sub_of_le hH] using
    assembly_trace_layer_le_scalar M h hγ Q k H0 hH0 hpast (H-H0,i) N weights ω

end
end ASDExplicitGamma.Inverse
