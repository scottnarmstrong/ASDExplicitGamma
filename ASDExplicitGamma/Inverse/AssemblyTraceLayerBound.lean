module

public import ASDExplicitGamma.Inverse.AssemblyActiveSpatialLayer
public import ASDExplicitGamma.Inverse.AssemblyIdentitySpatial
public import ASDExplicitGamma.Inverse.AssemblyTraceMatrixSeries

/-! A scalar positive mean-plus-error bound for every deterministic trace layer. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- Constant spatial payment on active cells. -/
def assemblyActiveConstant : ℝ := 1+32*(10*waveGateEta .allOrder)^2

/-- Deterministic trace baseline multiplying the exact layer volume. -/
def assemblyTraceBaseline : ℝ :=
  rootAssemblySensitivity*((29/25:ℝ)+
    12*(1+2*Real.sqrt 3*resetAllOrderTau)*(planarGradientCharge 40+1)*
      assemblyActiveConstant*densityMomentBudget (allOrderDensity:ℝ) 2 1324)

/-- Coefficient of the actual physical wave, retaining the square root of
the exact layer volume fraction. -/
def assemblyTraceWaveCoefficient : ℝ :=
  rootAssemblySensitivity*((29/100:ℝ)+
    12*(1+2*Real.sqrt 3*resetAllOrderTau)*(planarGradientCharge 40+1)*
      Real.sqrt (densityMomentBudget (allOrderDensity:ℝ) 4 1324))

/-- The complete scalar mean-plus-positive-error envelope at one deterministic
height/layer. This is defined before the stopped height is substituted. -/
def assemblyTraceScalarLayer (M : ABKModel 2) (Q : TriadicCube 2)
    (k H0 : ℕ) (hk : ℕ × ℕ) (N : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  let H := H0+hk.1
  let i := hk.2
  let w := sourceBandWeights (protectedOldLabel Q.scale k) weights
  let W := physicalMissingWave M (layerOldCutoff Q.scale H (i+1)) Q.scale N
    (cubeCorner Q 0) (cubeCorner Q 1) w ω
  let Y := fun m e => resetDensityExcess M Q H0 resetAllOrderTau (waveGateEta .allOrder)
    (allOrderDensity:ℝ) 1324 m hk e ω
  rootAssemblyClock M.gamma H (i+1)*
    (assemblyTraceBaseline*bankLayerWeight i+
      assemblyTraceWaveCoefficient*Real.sqrt (bankLayerWeight i)*W+
      rootAssemblySensitivity*assemblyTraceMatrixDeviation M Q H (i+1) N w ω+
      4*rootAssemblySensitivity*(1+2*Real.sqrt 3*resetAllOrderTau)*(planarGradientCharge 40+1)*
        (assemblyActiveConstant*(∑ e : Fin 3, Y 2 e)+W*(∑ e : Fin 3, Real.sqrt (Y 4 e))))

/-- The active spatial integrals on all three resolutions have their exact
rare means plus correlated positive excesses. -/
theorem assembly_active_spatial_sum_le_mean_excess
    (M : ABKModel 2) (Q : TriadicCube 2) (k H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    let W := physicalMissingWave M (layerOldCutoff Q.scale (H0+hk.1) (hk.2+1)) Q.scale N
      (cubeCorner Q 0) (cubeCorner Q 1) (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω
    let Y := fun m e => resetDensityExcess M Q H0 resetAllOrderTau (waveGateEta .allOrder)
      (allOrderDensity:ℝ) 1324 m hk e ω
    (∑ e : Fin 3, ∫ x in rootLayerCarrier Q (H0+hk.1) (hk.2+1),
      (layerResolutionDiameter M Q (H0+hk.1) resetAllOrderTau (waveGateEta .allOrder) (hk.2+1) e ω x)^2*
        assemblyActiveSpatialPayment M Q k (H0+hk.1) (hk.2+1) N weights ω x
        ∂normalizedCubeMeasure Q) ≤
      assemblyActiveConstant*(3*bankLayerWeight hk.2*densityMomentBudget (allOrderDensity:ℝ) 2 1324+
        ∑ e : Fin 3, Y 2 e)+
      W*(3*Real.sqrt (bankLayerWeight hk.2)*Real.sqrt (densityMomentBudget (allOrderDensity:ℝ) 4 1324)+
        ∑ e : Fin 3, Real.sqrt (Y 4 e)) := by
  dsimp only
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun e _ =>
    assembly_active_spatial_layer_le_mean_excess M Q k H0 hH0 hk e N weights ω)
  apply hh.trans_eq
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
    Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold assemblyActiveConstant
  ring

/-- The complete real layer payment is bounded by the scalar envelope. The
native past is used only to bound the actual old clipped matrix mean. -/
theorem assembly_trace_layer_le_scalar
    (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (k H0 : ℕ) (hH0 : heightEntrance k ≤ H0)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*k → nativeInductionState M h n)
    (hk : ℕ × ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    let H := H0+hk.1
    let i := hk.2
    let w := sourceBandWeights (protectedOldLabel Q.scale k) weights
    rootAssemblySensitivity*rootAssemblyClock M.gamma H (i+1)*
      assemblyShearedLayerTrace M Q H (i+1) N w ω+
    (4*rootAssemblySensitivity*(1+2*Real.sqrt 3*resetAllOrderTau))*
      (rootAssemblyClock M.gamma H (i+1)*(planarGradientCharge 40+1)*
        ∑ e : Fin 3, ∫ x in rootLayerCarrier Q H (i+1),
          (layerResolutionDiameter M Q H resetAllOrderTau (waveGateEta .allOrder) (i+1) e ω x)^2*
            assemblyActiveSpatialPayment M Q k H (i+1) N weights ω x
              ∂normalizedCubeMeasure Q) ≤
      assemblyTraceScalarLayer M Q k H0 hk N weights ω := by
  dsimp only
  let H := H0+hk.1
  let i := hk.2
  let w := sourceBandWeights (protectedOldLabel Q.scale k) weights
  let W := physicalMissingWave M (layerOldCutoff Q.scale H (i+1)) Q.scale N
    (cubeCorner Q 0) (cubeCorner Q 1) w ω
  have h333 : 333 ≤ H0 := by unfold heightEntrance at hH0; omega
  have hmean := assembly_sheared_layer_mean_bound M h hγ Q k H (by dsimp only [H]; omega)
    hpast i N w ω
  have hwave := assembly_layer_mean_square_le_physical_wave M Q H i N w ω
  have hid := hmean.trans (add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (div_le_div_of_nonneg_right hwave (by norm_num : (0:ℝ) ≤ 2)))
      (by norm_num : (0:ℝ) ≤ 29/25)) le_rfl)
  have ha := assembly_active_spatial_sum_le_mean_excess M Q k H0 h333 hk N weights ω
  have hτ : 0 ≤ resetAllOrderTau := by norm_num [resetAllOrderTau,Numerics.Wave.allOrderTau]
  have hS : 0 ≤ planarGradientCharge 40+1 := by unfold planarGradientCharge; positivity
  have hc := (root_assembly_clock_pos M.gamma H (i+1)).le
  have hs := root_assembly_sensitivity_pos.le
  have hi := mul_le_mul_of_nonneg_left hid (mul_nonneg hs hc)
  have haa := mul_le_mul_of_nonneg_left ha
    (show 0 ≤ (4*rootAssemblySensitivity*(1+2*Real.sqrt 3*resetAllOrderTau))*
      (rootAssemblyClock M.gamma H (i+1)*(planarGradientCharge 40+1)) by positivity)
  convert add_le_add hi haa using 1 <;>
    dsimp only [assemblyTraceScalarLayer,assemblyTraceBaseline,assemblyTraceWaveCoefficient,
      assemblyTraceMatrixDeviation,assemblyActiveConstant,H,i,w,W] <;> ring

end
end ASDExplicitGamma.Inverse
