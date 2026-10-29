module

public import ASDExplicitGamma.Inverse.FullResponseActiveLayerMean
public import ASDExplicitGamma.Inverse.PhysicalGaussianReconstruction

/-! Exact identification of the layer wave in the physical reset normalization. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic

noncomputable section

/-- The geometric Whitney old label is exactly the physical reset old label. -/
theorem full_response_layer_old_label_eq_physical (Q : TriadicCube 2)
    (H0 : ℕ) (hH0 : 38 ≤ H0) (hk : ℕ × ℕ) :
    rootLayerOldLabel Q H0 hk = physicalResetOldLabel Q H0 hk := by
  have hx := localization_reset_abscissa_source H0 hk.1 hk.2 hH0
  unfold rootLayerOldLabel physicalResetOldLabel
  push_cast
  omega

/-- The scalar fourth moment in the active layer is exactly half of the
physical Frobenius missing-wave statistic in that same true frame. -/
theorem full_response_layer_wave_fourth_eq_physical
    (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 38 ≤ H0)
    (hk : ℕ × ℕ) (m J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    2*fullResponseLayerWaveFourth M Q H0 hk m J weights ω =
      physicalMissingWave M (physicalResetOldLabel Q H0 hk) Q.scale J
        (cubeCorner Q 0) (cubeCorner Q 1) (sourceBandWeights m weights) ω := by
  rw [later_band_physical_missing_wave_eq_fourth_average]
  unfold fullResponseLayerWaveFourth
  rw [full_response_layer_old_label_eq_physical Q H0 hH0 hk]
  ring

/-- The actual wave and frame clock reconstruct the source reset term,
including the factor one half and the complete D+x gap. The endpoint J=l-1
is included because every protected old label is strictly earlier. -/
theorem full_response_layer_wave_reconstruction
    (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (m J : ℤ) (hJ : Q.scale-1 ≤ J) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    let x := (localizationResetAbscissa (H0-38) hk.1 hk.2 : ℝ)
    let D := (J:ℝ)-(Q.scale:ℝ)+1
    (3:ℝ)^(2*M.gamma*x)*fullResponseLayerWaveFourth M Q H0 hk m J weights ω =
      (M.gamma*(D+x)*(3:ℝ)^(2*M.gamma*D)/2) *
        physicalResetWave M Q J H0 (cubeCorner Q 0) (cubeCorner Q 1)
          (fun _ => sourceBandWeights m weights) hk ω := by
  dsimp only
  let j := physicalResetOldLabel Q H0 hk
  let x := (localizationResetAbscissa (H0-38) hk.1 hk.2 : ℝ)
  let D := (J:ℝ)-(Q.scale:ℝ)+1
  let V := physicalMissingWave M j Q.scale J (cubeCorner Q 0) (cubeCorner Q 1)
    (sourceBandWeights m weights) ω
  have hjJ : j < J := by
    dsimp only [j, physicalResetOldLabel, localizationResetAbscissa, localizationProfileDepth]
    omega
  have hgap : (0:ℝ) < (J:ℝ)-(j:ℝ) := by exact_mod_cast sub_pos.mpr hjJ
  have hxgap : (J:ℝ)-(j:ℝ) = D+x := physical_reset_gap_eq Q J H0 hk
  have hV : fullResponseLayerWaveFourth M Q H0 hk m J weights ω = V/2 := by
    have he := full_response_layer_wave_fourth_eq_physical M Q H0 (by omega)
      hk m J weights ω
    change 2*fullResponseLayerWaveFourth M Q H0 hk m J weights ω = V at he
    linarith only [he]
  rw [hV]
  change (3:ℝ)^(2*M.gamma*x)*(V/2) =
    (M.gamma*(D+x)*(3:ℝ)^(2*M.gamma*D)/2) *
      ((3:ℝ)^(2*M.gamma*(x-D))/(M.gamma*((J:ℝ)-(j:ℝ)))*V)
  rw [← hxgap]
  have hr : (3:ℝ)^(2*M.gamma*D)*(3:ℝ)^(2*M.gamma*(x-D)) =
      (3:ℝ)^(2*M.gamma*x) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    ring
  field_simp [M.shellPrefix.gamma_pos.ne', hgap.ne']
  linear_combination -V*hr

/-- The leading layer wave splits into exactly the source's two height
profiles: the unweighted W₀ term and the first height moment W₁ term. -/
theorem full_response_height_layer_wave_reconstruction
    (M : ABKModel 2) (Q : TriadicCube 2) (H0 H layer : ℕ)
    (hH0 : 333 ≤ H0) (hH : H0 ≤ H) (m J : ℤ) (hJ : Q.scale-1 ≤ J)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    let x := (localizationResetAbscissa (H0-38) (H-H0) layer : ℝ)
    let f := (localizationProfileDepth (layer+1) : ℝ)
    let D := (J:ℝ)-(Q.scale:ℝ)+1
    (3:ℝ)^(2*M.gamma*x) *
        fullResponseLayerWaveFourth M Q H0 (H-H0,layer) m J weights ω =
      (M.gamma*(3:ℝ)^(2*M.gamma*D)/2) * (3:ℝ)^(4*M.gamma*f) *
        ((D+f)*physicalHeightWave M Q J H0 (cubeCorner Q 0) (cubeCorner Q 1)
            (fun _ => sourceBandWeights m weights) layer H ω +
          physicalHeightWeightedWave M Q J H0 (cubeCorner Q 0) (cubeCorner Q 1)
            (fun _ => sourceBandWeights m weights) layer 1 H ω) := by
  dsimp only
  rw [full_response_layer_wave_reconstruction M Q H0 hH0 (H-H0,layer) m J hJ weights ω,
    ← physical_height_wave_reconstruction M Q J H0 (cubeCorner Q 0) (cubeCorner Q 1)
      (fun _ => sourceBandWeights m weights) layer H ω,
    physical_height_abscissa_eq H0 (by omega) H hH layer]
  simp only [physicalHeightWeightedWave, Fin.val_one, pow_one]
  ring

end
end ASDExplicitGamma.Inverse
