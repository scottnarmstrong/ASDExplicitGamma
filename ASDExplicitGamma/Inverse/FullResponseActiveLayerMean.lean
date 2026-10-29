module

public import ASDExplicitGamma.Inverse.FullResponseActiveObserverMean
public import ASDExplicitGamma.Inverse.FullResponseLayerWaveDensity

/-! Active trace layer coefficients with their actual positive density errors. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model

noncomputable section

/-- The normalized scalar fourth-moment root of the layer's actual later band. -/
def fullResponseLayerWaveFourth (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (hk : ℕ × ℕ) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  let n := rootLayerOldLabel Q H0 hk
  Real.sqrt (cubeAverage Q (fun x =>
    laterScalarBand n J (sourceBandWeights m weights) ω x^4)) /
      (Annealed.sigmaBar M n : ℝ)^2

/-- Every parent's wave mean on one deterministic layer uses the same old
label, so spatial Holder applies before the random height is selected. -/
theorem full_response_parent_wave_density_layer_le
    (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (τ η q T : ℝ) (e : Fin 3) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    let d := layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω
    (∑ U ∈ whitneyRootLayer Q (H0+hk.1) (hk.2+1),
      ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) *
        ((fullResponseParentWaveMean M U m J weights ω)^2 *
          cubeAverage U (fun x => d x^2))) ≤
      fullResponseLayerWaveFourth M Q H0 hk m J weights ω *
        (Real.sqrt (bankLayerWeight hk.2)*Real.sqrt (densityMomentBudget q 4 T) +
          Real.sqrt (resetDensityExcess M Q H0 τ η q T 4 hk e ω)) := by
  classical
  dsimp only
  let n := rootLayerOldLabel Q H0 hk
  let σ := (Annealed.sigmaBar M n : ℝ)
  let f := laterScalarBand n J (sourceBandWeights m weights) ω
  let d := layerResolutionDiameter M Q (H0+hk.1) τ η (hk.2+1) e ω
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hlabel (U : TriadicCube 2) (hU : U ∈ whitneyRootLayer Q (H0+hk.1) (hk.2+1)) :
      U.scale+40=n := by
    have hh := root_whitney_layer_scale Q (H0+hk.1) (hk.2+1) hU
    dsimp only [n, rootLayerOldLabel, resetDepth]
    unfold whitneyProfile at hh
    omega
  have hraw := layer_later_band_density_le_mean_add_excess
    M Q H0 hH0 hk τ η q T e n J (sourceBandWeights m weights) ω
  have hscaled := mul_le_mul_of_nonneg_left hraw
    (by positivity : (0:ℝ) ≤ 1/σ^2)
  have hleft : (∑ U ∈ whitneyRootLayer Q (H0+hk.1) (hk.2+1),
      ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) *
        ((fullResponseParentWaveMean M U m J weights ω)^2 * cubeAverage U (fun x => d x^2))) =
      (1/σ^2) * ∑ U ∈ whitneyRootLayer Q (H0+hk.1) (hk.2+1),
        ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) *
          ((cubeAverage U f)^2 * cubeAverage U (fun x => d x^2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro U hU
    dsimp only [fullResponseParentWaveMean]
    rw [hlabel U hU]
    change _ * ((cubeAverage U f/σ)^2 * _) = _
    rw [div_pow]
    ring
  rw [hleft]
  apply hscaled.trans_eq
  dsimp only [fullResponseLayerWaveFourth, n, σ, f]
  ring

/-- The source c₀ₜ/c₁ₜ active layer is its precise rare-mean baseline,
wave fourth moment, and the actual D2/D4 positive excesses. -/
theorem full_response_active_layer_mean_add_excess
    (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (q T : ℝ) (e : Fin 3) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    let d := layerResolutionDiameter M Q (H0+hk.1)
      (rootTau .full) (waveGateEta .full) (hk.2+1) e ω
    (∑ U ∈ whitneyRootLayer Q (H0+hk.1) (hk.2+1),
      ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) *
        (fullResponseTraceC0 + fullResponseTraceC1*
          (fullResponseParentWaveMean M U m J weights ω)^2) *
            cubeAverage U (fun x => d x^2)) ≤
      fullResponseTraceC0*(bankLayerWeight hk.2*densityMomentBudget q 2 T +
        resetDensityExcess M Q H0 (rootTau .full) (waveGateEta .full) q T 2 hk e ω) +
      fullResponseTraceC1*fullResponseLayerWaveFourth M Q H0 hk m J weights ω *
        (Real.sqrt (bankLayerWeight hk.2)*Real.sqrt (densityMomentBudget q 4 T) +
          Real.sqrt (resetDensityExcess M Q H0 (rootTau .full)
            (waveGateEta .full) q T 4 hk e ω)) := by
  classical
  dsimp only
  let d := layerResolutionDiameter M Q (H0+hk.1)
    (rootTau .full) (waveGateEta .full) (hk.2+1) e ω
  have hdint := layer_resolution_square_integrableOn M Q H0 hH0 hk
    (rootTau .full) (waveGateEta .full) e ω
  have hbase := (root_layer_weighted_cube_average_eq Q (H0+hk.1) hk.2
    (fun x => d x^2) hdint).trans_le
      (layer_resolution_average_le_excess M Q H0 hH0 hk
        (rootTau .full) (waveGateEta .full) q T e ω)
  have hwave := full_response_parent_wave_density_layer_le M Q H0 hH0 hk
    (rootTau .full) (waveGateEta .full) q T e m J weights ω
  have hc0 : 0 ≤ fullResponseTraceC0 := by
    dsimp only [fullResponseTraceC0, rootTau]
    positivity
  have hc1 : 0 ≤ fullResponseTraceC1 := by
    norm_num [fullResponseTraceC1, rootTau]
  have hh := add_le_add (mul_le_mul_of_nonneg_left hbase hc0)
    (mul_le_mul_of_nonneg_left hwave hc1)
  calc
    _ = fullResponseTraceC0 *
        (∑ U ∈ whitneyRootLayer Q (H0+hk.1) (hk.2+1),
          ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) * cubeAverage U (fun x => d x^2)) +
      fullResponseTraceC1 *
        (∑ U ∈ whitneyRootLayer Q (H0+hk.1) (hk.2+1),
          ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) *
            ((fullResponseParentWaveMean M U m J weights ω)^2 * cubeAverage U (fun x => d x^2))) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro U hU
      ring
    _ ≤ _ := hh.trans_eq (by ring)

end
end ASDExplicitGamma.Inverse
