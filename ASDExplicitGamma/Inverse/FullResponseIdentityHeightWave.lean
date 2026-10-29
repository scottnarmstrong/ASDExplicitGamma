module

public import ASDExplicitGamma.Inverse.FullResponseIdentityLayerWaveMoments
public import ASDExplicitGamma.Inverse.FullResponseLayerWavePhysical

/-! The normalized identity-layer wave at the fixed full-response entrance. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal

noncomputable section

/-- Every actual planar Whitney layer has strictly positive volume fraction. -/
theorem full_response_layer_weight_pos (k : ℕ) : 0 < bankLayerWeight k := by
  cases k with
  | zero => norm_num [layerWeight_zero]
  | succ k =>
    rw [layerWeight_succ]
    let u := (1/3:ℝ)^(k+2)
    have hu : 0 < u := by dsimp only [u]; positivity
    have hp : (1/3:ℝ)^k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hule : u ≤ 1/9 := by
      dsimp only [u]
      rw [pow_add]
      norm_num
      nlinarith only [hp]
    have he : (1/9:ℝ)^(k+2)=u^2 := by
      dsimp only [u]
      rw [← pow_mul, Nat.mul_comm (k+2) 2, pow_mul]
      norm_num
    rw [he]
    change 0 < 8*u-32*u^2
    have hh := mul_pos (by positivity : (0:ℝ)<8*u) (by linarith only [hule] : 0<1-4*u)
    nlinarith only [hh]

/-- Twice the weighted local squared shear means divided by vₖ, with the
same reversible frame and layer normalization as the physical wave profile. -/
def fullResponseIdentityHeightWave (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (layer H : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let old := layerOldCutoff Q.scale H (layer+1)
  let x := (localizationResetAbscissa (377-38) (H-377) layer : ℝ)
  let D := (N:ℝ)-(Q.scale:ℝ)+1
  ((3:ℝ)^(-4*M.gamma*(localizationProfileDepth (layer+1):ℝ)) *
    ((3:ℝ)^(2*M.gamma*(x-D))/(M.gamma*(N-old:ℝ))) * (2/bankLayerWeight layer)) *
      assemblyLayerMeanSquare M Q H (layer+1) N
        (sourceBandWeights (Q.scale-342) weights) ω

/-- The actual normalized identity family has the source ordinary wave
moments, including the endpoint terminal label N=l-1. -/
theorem full_response_identity_height_wave_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-342, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (layer H : ℕ) (hH : 377 ≤ H) (p : ℝ) (hp : 1 ≤ p) :
    Measurable (fullResponseIdentityHeightWave M Q N weights layer H) ∧
      eLpNorm (fullResponseIdentityHeightWave M Q N weights layer H)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal (40*(p+2)*(3:ℝ)^(4*M.gamma*((H:ℝ)-38))) := by
  let old := layerOldCutoff Q.scale H (layer+1)
  let x := (localizationResetAbscissa (377-38) (H-377) layer : ℝ)
  let D := (N:ℝ)-(Q.scale:ℝ)+1
  let Δ := (N-old:ℝ)
  let f := (localizationProfileDepth (layer+1):ℝ)
  let C := (3:ℝ)^(-4*M.gamma*f) *
    ((3:ℝ)^(2*M.gamma*(x-D))/(M.gamma*Δ)) * (2/bankLayerWeight layer)
  have hH0 : heightEntrance 0 ≤ H := by
    simpa only [heightEntrance, mul_zero, add_zero] using hH
  have hold : old ≤ Q.scale-342 := by
    simpa only [old, protectedOldLabel, Nat.cast_zero, mul_zero, sub_zero] using
      layer_old_cutoff_le_protected Q.scale 0 H (layer+1) hH0 (by omega)
  have hstrict : old < N := by omega
  have hΔ : 0 < Δ := by dsimp only [Δ]; exact_mod_cast sub_pos.mpr hstrict
  have hv := full_response_layer_weight_pos layer
  have hC : 0 ≤ C := by
    have hγ := M.shellPrefix.gamma_pos
    dsimp only [C]
    positivity
  have hb := full_response_identity_layer_wave_Lp M h hM Q H hH hpast
    layer N hN weights hw p hp
  have he : fullResponseIdentityHeightWave M Q N weights layer H =
      C • assemblyLayerMeanSquare M Q H (layer+1) N
        (sourceBandWeights (Q.scale-342) weights) := rfl
  rw [he]
  refine ⟨hb.1.const_mul C, ?_⟩
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hC]
  apply (mul_le_mul_of_nonneg_left hb.2 (show 0 ≤ ENNReal.ofReal C from bot_le)).trans_eq
  rw [← ENNReal.ofReal_mul hC]
  congr 1
  have hx : layerRelativeOffset H (layer+1) =
      localizationResetAbscissa (377-38) (H-377) layer := by
    unfold layerRelativeOffset layerProfile localizationResetAbscissa localizationProfileDepth
    omega
  have hgap : Δ = D+x := by
    dsimp only [Δ, old]
    rw [layer_old_cutoff_eq_source_offset Q.scale H (layer+1) (by omega) (by omega), hx]
    dsimp only [D, x]
    push_cast
    ring
  have hxreal : x=((H:ℝ)-38)+f :=
    physical_height_abscissa_eq 377 (by norm_num) H hH layer
  have hr : (3:ℝ)^(-4*M.gamma*f) * (3:ℝ)^(2*M.gamma*(x-D)) *
      (3:ℝ)^(2*M.gamma*Δ) = (3:ℝ)^(4*M.gamma*((H:ℝ)-38)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ)<3),
      ← Real.rpow_add (by norm_num : (0:ℝ)<3)]
    congr 1
    rw [hgap, hxreal]
    ring
  change C*(bankLayerWeight layer*20*(p+2)*(M.gamma*Δ*(3:ℝ)^(2*M.gamma*Δ))) = _
  dsimp only [C]
  calc
    _ = 40*(p+2)*((3:ℝ)^(-4*M.gamma*f) *
        (3:ℝ)^(2*M.gamma*(x-D)) * (3:ℝ)^(2*M.gamma*Δ)) := by
      field_simp [M.shellPrefix.gamma_pos.ne', hΔ.ne', hv.ne']
      ring
    _ = _ := by rw [hr]

/-- The two source height moments; below the entrance the family is extended
constantly so that its measurability has no artificial height hypothesis. -/
def fullResponseIdentityWeightedWave (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (layer : ℕ) (j : Fin 2) (H : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (((max 377 H : ℕ):ℝ)-38)^j.val *
    fullResponseIdentityHeightWave M Q N weights layer (max 377 H) ω

/-- Both ordinary height moments retain the literal source wave budget. -/
theorem full_response_identity_weighted_wave_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-342, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights k ∧ weights k ≤ 1)
    (layer : ℕ) (j : Fin 2) (H : ℕ) (hH : 377 ≤ H) (p : ℝ) (hp : 1 ≤ p) :
    Measurable (fullResponseIdentityWeightedWave M Q N weights layer j H) ∧
      eLpNorm (fullResponseIdentityWeightedWave M Q N weights layer j H)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
          ENNReal.ofReal (40*(p+2)*((H:ℝ)-38)^j.val*
            (3:ℝ)^(4*M.gamma*((H:ℝ)-38))) := by
  have hb := full_response_identity_height_wave_Lp M h hM Q hpast N hN weights hw layer H hH p hp
  have hz : (0:ℝ) ≤ (H:ℝ)-38 := by
    have hh : (377:ℝ) ≤ H := by exact_mod_cast hH
    linarith only [hh]
  have hC := pow_nonneg hz j.val
  have he : fullResponseIdentityWeightedWave M Q N weights layer j H =
      ((H:ℝ)-38)^j.val • fullResponseIdentityHeightWave M Q N weights layer H := by
    funext ω
    simp only [fullResponseIdentityWeightedWave, max_eq_right hH, Pi.smul_apply,
      smul_eq_mul]
  rw [he]
  refine ⟨hb.1.const_mul _, ?_⟩
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hC]
  apply (mul_le_mul_of_nonneg_left hb.2 (zero_le : (0:ℝ≥0∞) ≤ _)).trans_eq
  rw [← ENNReal.ofReal_mul hC]
  congr 1
  ring

/-- The height-indexed identity family is measurable at every height. -/
theorem full_response_identity_weighted_wave_measurable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-342, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights k ∧ weights k ≤ 1)
    (layer : ℕ) (j : Fin 2) (H : ℕ) :
    Measurable (fullResponseIdentityWeightedWave M Q N weights layer j H) := by
  have hb := (full_response_identity_height_wave_Lp M h hM Q hpast N hN weights hw
    layer (max 377 H) (le_max_left _ _) 1 le_rfl).1
  exact hb.const_mul _

end
end ASDExplicitGamma.Inverse
