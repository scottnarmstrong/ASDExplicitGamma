module

public import ASDExplicitGamma.Inverse.FullResponseMissingWaveMoments
public import ASDExplicitGamma.Inverse.PhysicalGaussianHeightWave

/-! Endpoint-compatible ordinary physical wave moments for the full response. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The physical reset-wave estimate includes the terminal endpoint N=l-1. -/
theorem full_response_reset_wave_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale-1 ≤ N) (H0 : ℕ) (hH : 333 ≤ H0)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc (physicalResetOldLabel Q H0 hk) N, 0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (hk : ℕ × ℕ) (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (physicalResetWave A Q N H0 a c weights hk) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤
      ENNReal.ofReal (40*(p+2)*(3:ℝ)^(4*A.gamma*(localizationResetAbscissa (H0-38) hk.1 hk.2:ℝ))) := by
  let j := physicalResetOldLabel Q H0 hk
  let x : ℝ := localizationResetAbscissa (H0-38) hk.1 hk.2
  let D : ℝ := (N:ℝ)-(Q.scale:ℝ)+1
  let Δ : ℝ := (N:ℝ)-(j:ℝ)
  let C := (3:ℝ)^(2*A.gamma*(x-D))/(A.gamma*Δ)
  have hjN : j < N := by
    dsimp only [j,physicalResetOldLabel,localizationResetAbscissa,localizationProfileDepth]
    omega
  have hΔ : 0 < Δ := by dsimp only [Δ]; exact_mod_cast sub_pos.mpr hjN
  have hden : 0 < A.gamma*Δ := mul_pos A.shellPrefix.gamma_pos hΔ
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hg : Δ = D+x := physical_reset_gap_eq Q N H0 hk
  have hsource := full_response_missing_wave_Lp A h hA j Q.scale N hjN
    (hpast j (physical_reset_old_label_protected Q H0 hH hk)) a c (weights hk) (hw hk) p hp
  have he : physicalResetWave A Q N H0 a c weights hk = C • physicalMissingWave A j Q.scale N a c (weights hk) := by
    funext ω
    rfl
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal hC]
  apply (mul_le_mul_of_nonneg_left hsource (zero_le : (0:ℝ≥0∞) ≤ _)).trans_eq
  rw [← ENNReal.ofReal_mul hC]
  congr 1
  change C*(40*(p+2)*(A.gamma*Δ*(3:ℝ)^(2*A.gamma*Δ))) = _
  calc
    _ = 40*(p+2)*((3:ℝ)^(2*A.gamma*(x-D))*(3:ℝ)^(2*A.gamma*Δ)) := by
      dsimp only [C]
      field_simp [A.shellPrefix.gamma_pos.ne',hΔ.ne']
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3),hg]
      congr 1
      dsimp only [x]
      ring_nf


/-- The normalized ordinary height wave at the same endpoint. -/
theorem full_response_height_wave_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale-1 ≤ N) (H0 : ℕ) (hH : 333 ≤ H0)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc (physicalResetOldLabel Q H0 hk) N, 0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (layer H : ℕ) (hH0 : H0 ≤ H) (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (physicalHeightWave A Q N H0 a c weights layer H) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤
      ENNReal.ofReal (40*(p+2)*(3:ℝ)^(4*A.gamma*((H:ℝ)-38))) := by
  let C := (3:ℝ)^(-4*A.gamma*(localizationProfileDepth (layer+1):ℝ))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hx := physical_height_abscissa_eq H0 (by omega) H hH0 layer
  have hh := full_response_reset_wave_Lp A h hA Q N hQN H0 hH hpast a c weights hw (H-H0,layer) p hp
  have he : physicalHeightWave A Q N H0 a c weights layer H =
      C • physicalResetWave A Q N H0 a c weights (H-H0,layer) := by funext ω; rfl
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal hC]
  apply (mul_le_mul_of_nonneg_left hh (zero_le : (0:ℝ≥0∞) ≤ _)).trans_eq
  rw [← ENNReal.ofReal_mul hC]
  congr 1
  change C*(40*(p+2)*(3:ℝ)^(4*A.gamma*(localizationResetAbscissa (H0-38) (H-H0) layer:ℝ))) = _
  calc
    _ = 40*(p+2)*((3:ℝ)^(-4*A.gamma*(localizationProfileDepth (layer+1):ℝ))*
        (3:ℝ)^(4*A.gamma*(localizationResetAbscissa (H0-38) (H-H0) layer:ℝ))) := by dsimp only [C]; ring
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3),hx]
      congr 1
      ring_nf

/-- The literal z_h^j wave moment at every deterministic candidate height. -/
theorem full_response_height_weighted_wave_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale-1 ≤ N) (H0 : ℕ) (hH : 333 ≤ H0)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+40, nativeInductionState A h k)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc (physicalResetOldLabel Q H0 hk) N, 0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (layer : ℕ) (j : Fin 2) (H : ℕ) (hH0 : H0 ≤ H) (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (physicalHeightWeightedWave A Q N H0 a c weights layer j H) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤
      ENNReal.ofReal (40*(p+2)*((H:ℝ)-38)^j.val*(3:ℝ)^(4*A.gamma*((H:ℝ)-38))) := by
  have hz : (0:ℝ) ≤ (H:ℝ)-38 := by
    have hHr : (333:ℝ) ≤ H := by exact_mod_cast (le_trans hH hH0)
    linarith only [hHr]
  have hC : 0 ≤ ((H:ℝ)-38)^j.val := pow_nonneg hz _
  have he : physicalHeightWeightedWave A Q N H0 a c weights layer j H =
      ((H:ℝ)-38)^j.val • physicalHeightWave A Q N H0 a c weights layer H := by funext ω; rfl
  rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal hC]
  apply (mul_le_mul_of_nonneg_left (full_response_height_wave_Lp A h hA Q N hQN H0 hH hpast a c weights hw
    layer H hH0 p hp) (zero_le : (0:ℝ≥0∞) ≤ _)).trans_eq
  rw [← ENNReal.ofReal_mul hC]
  congr 1
  ring

end
end ASDExplicitGamma.Inverse
