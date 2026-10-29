module

public import ASDExplicitGamma.Inverse.AssemblySpatialHolder

/-! Positive rare-mean and correlated-excess payments on an actual layer. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- The actual squared-density spatial payment splits exactly into its
constant and squared-wave pieces before applying any probability estimate. -/
theorem assembly_actual_spatial_payment_integral
    (M : ABKModel 2) (Q : TriadicCube 2) (k H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (e : Fin 3) (N : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    let j := layerOldCutoff Q.scale (H0+hk.1) (hk.2+1)
    let f := laterScalarBand j N (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω
    let g := layerResolutionDiameter M Q (H0+hk.1) resetAllOrderTau (waveGateEta .allOrder)
      (hk.2+1) e ω
    let E := rootLayerCarrier Q (H0+hk.1) (hk.2+1)
    (∫ x in E, g x^2*assemblyActiveSpatialPayment M Q k (H0+hk.1) (hk.2+1) N weights ω x
      ∂normalizedCubeMeasure Q) =
      (1+32*(10*waveGateEta .allOrder)^2)*(∫ x in E, g x^2 ∂normalizedCubeMeasure Q)+
        (2/(Annealed.sigmaBar M j)^2)*(∫ x in E, f x^2*g x^2 ∂normalizedCubeMeasure Q) := by
  dsimp only
  let μ := normalizedCubeMeasure Q
  let E := rootLayerCarrier Q (H0+hk.1) (hk.2+1)
  let j := layerOldCutoff Q.scale (H0+hk.1) (hk.2+1)
  let f := laterScalarBand j N (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω
  let g := layerResolutionDiameter M Q (H0+hk.1) resetAllOrderTau (waveGateEta .allOrder)
    (hk.2+1) e ω
  have hf : MemLp f ⊤ μ := by
    change MemLp (laterScalarBand j N (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω) ⊤ (normalizedCubeMeasure Q)
    rw [← later_band_w2_value Q j N (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω]
    exact PlanarW2Infinity.value_memLp_top_normalized _
  have hf2 := assembly_square_memLp_two μ f hf
  have hg2 : MemLp (fun x => g x^2) 2 μ :=
    layer_resolution_density_square_memLp M Q Q (fun _ hx => hx) H0 hH0 hk
      resetAllOrderTau (waveGateEta .allOrder) e ω
  have hi1 := (hg2.restrict E).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hi2 := (hf2.restrict E).integrable_mul (hg2.restrict E)
  change Integrable (fun x => f x^2*g x^2) (μ.restrict E) at hi2
  calc
    _ = ∫ x in E, (1+32*(10*waveGateEta .allOrder)^2)*g x^2+
        (2/(Annealed.sigmaBar M j)^2)*(f x^2*g x^2) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      change g x^2*(1+32*(10*waveGateEta .allOrder)^2+2*(f x/Annealed.sigmaBar M j)^2)=_
      rw [div_pow]
      ring
    _ = _ := by
      rw [integral_add (hi1.const_mul _) (hi2.const_mul _),integral_const_mul,integral_const_mul]

/-- Actual active spatial payments are bounded by a positive rare second
moment, its actual excess, and a physical missing wave paired with the rare
fourth moment and actual square-root excess. -/
theorem assembly_active_spatial_layer_le_mean_excess
    (M : ABKModel 2) (Q : TriadicCube 2) (k H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (e : Fin 3) (N : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    let j := layerOldCutoff Q.scale (H0+hk.1) (hk.2+1)
    let w := sourceBandWeights (protectedOldLabel Q.scale k) weights
    let g := layerResolutionDiameter M Q (H0+hk.1) resetAllOrderTau (waveGateEta .allOrder)
      (hk.2+1) e ω
    let E := rootLayerCarrier Q (H0+hk.1) (hk.2+1)
    (∫ x in E, g x^2*assemblyActiveSpatialPayment M Q k (H0+hk.1) (hk.2+1) N weights ω x
      ∂normalizedCubeMeasure Q) ≤
      (1+32*(10*waveGateEta .allOrder)^2)*
        (bankLayerWeight hk.2*densityMomentBudget (allOrderDensity:ℝ) 2 1324+
          resetDensityExcess M Q H0 resetAllOrderTau (waveGateEta .allOrder)
            (allOrderDensity:ℝ) 1324 2 hk e ω)+
      physicalMissingWave M j Q.scale N (cubeCorner Q 0) (cubeCorner Q 1) w ω*
        (Real.sqrt (bankLayerWeight hk.2)*Real.sqrt (densityMomentBudget (allOrderDensity:ℝ) 4 1324)+
          Real.sqrt (resetDensityExcess M Q H0 resetAllOrderTau (waveGateEta .allOrder)
            (allOrderDensity:ℝ) 1324 4 hk e ω)) := by
  dsimp only
  rw [assembly_actual_spatial_payment_integral M Q k H0 hH0 hk e N weights ω]
  have hd := assembly_normalized_density_power_le_excess M Q H0 hH0 hk resetAllOrderTau
    (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 2 e ω
  have hq : 0 ≤ (allOrderDensity:ℝ) := by norm_num [allOrderDensity]
  have hb := density_moment_budget_nonneg (allOrderDensity:ℝ) hq 4 1324 (by norm_num)
  have hw := assembly_actual_wave_density_le_mean_excess M Q H0 hH0 hk resetAllOrderTau
    (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 hb e
    (layerOldCutoff Q.scale (H0+hk.1) (hk.2+1)) N
    (sourceBandWeights (protectedOldLabel Q.scale k) weights) ω
  rw [later_band_physical_missing_wave_eq_fourth_average]
  exact add_le_add (mul_le_mul_of_nonneg_left hd (by positivity))
    ((mul_le_mul_of_nonneg_left hw (by positivity)).trans_eq (by ring))

end
end ASDExplicitGamma.Inverse
