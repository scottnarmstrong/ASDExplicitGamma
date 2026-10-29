module

public import ASDExplicitGamma.Inverse.PhysicalWave
public import ASDExplicitGamma.Inverse.AllOrderStoppedGeometry
public import ASDExplicitGamma.Inverse.PhysicalGaussianAllOrderTail
public import ASDExplicitGamma.Inverse.PhysicalGaussianHeightWave
public import ASDExplicitGamma.Inverse.StoppedSelectedWaveExactFamily
public import ASDExplicitGamma.Inverse.PhysicalGaussianSelectedWave
public import ASDExplicitGamma.Inverse.PhysicalGaussianCorrelatedSeries

/-! Selected physical waves at the exact layer height and protected labels. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- The first layer has old label l-H0+35, including its five fixed generations. -/
theorem reset_old_label_protected (Q : TriadicCube 2) (H0 : ℕ)
    (hH : 38 ≤ H0) (hk : ℕ × ℕ) :
    physicalResetOldLabel Q H0 hk ≤ Q.scale-(H0:ℤ)+35 := by
  unfold physicalResetOldLabel localizationResetAbscissa localizationProfileDepth
  omega

theorem physical_reset_wave_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale-1 ≤ N) (H0 : ℕ) (hH : 333 ≤ H0)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+35, nativeInductionState A h k)
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
  have hjn : j ≤ Q.scale := (physical_reset_old_label_lt Q H0 hk).le
  have hprotected := reset_old_label_protected Q H0 (by omega) hk
  have hjN : j < N := by
    dsimp only [j]
    omega
  have hΔ : 0 < Δ := by dsimp only [Δ]; exact_mod_cast sub_pos.mpr hjN
  have hden : 0 < A.gamma*Δ := mul_pos A.shellPrefix.gamma_pos hΔ
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hg : Δ = D+x := physical_reset_gap_eq Q N H0 hk
  have hsource := physical_missing_wave_Lp A h hA j Q.scale N hjN.le
    (hpast j (reset_old_label_protected Q H0 (by omega) hk)) a c (weights hk) (hw hk) p hp
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


theorem physical_height_wave_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale-1 ≤ N) (H0 : ℕ) (hH : 333 ≤ H0)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+35, nativeInductionState A h k)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc (physicalResetOldLabel Q H0 hk) N, 0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (layer H : ℕ) (hH0 : H0 ≤ H) (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (physicalHeightWave A Q N H0 a c weights layer H) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤
      ENNReal.ofReal (40*(p+2)*(3:ℝ)^(4*A.gamma*((H:ℝ)-38))) := by
  let C := (3:ℝ)^(-4*A.gamma*(localizationProfileDepth (layer+1):ℝ))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hx := physical_height_abscissa_eq H0 (by omega) H hH0 layer
  have hh := physical_reset_wave_Lp A h hA Q N hQN H0 hH hpast a c weights hw (H-H0,layer) p hp
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
theorem physical_height_weighted_wave_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale-1 ≤ N) (H0 : ℕ) (hH : 333 ≤ H0)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+35, nativeInductionState A h k)
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
  apply (mul_le_mul_of_nonneg_left (physical_height_wave_Lp A h hA Q N hQN H0 hH hpast a c weights hw
    layer H hH0 p hp) (zero_le : (0:ℝ≥0∞) ≤ _)).trans_eq
  rw [← ENNReal.ofReal_mul hC]
  congr 1
  ring


/-- The twelve source candidates share one ordinary physical-wave cap. -/
theorem physical_height_wave_candidate_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (Q : TriadicCube 2) (N : ℤ) (hQN : Q.scale-1 ≤ N) (H0 : ℕ) (hH : 333 ≤ H0)
    (hpast : ∀ k ≤ Q.scale-(H0:ℤ)+35, nativeInductionState A h k)
    (a c : ℝ) (weights : (ℕ × ℕ) → ℤ → ℝ)
    (hw : ∀ hk, ∀ k ∈ Finset.Ioc (physicalResetOldLabel Q H0 hk) N, 0 ≤ weights hk k ∧ weights hk k ≤ 1)
    (layer : ℕ) (j : Fin 2) (H : ℕ) (hHC : H ∈ selectedCandidateHeights H0)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (physicalHeightWeightedWave A Q N H0 a c weights layer j H) (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw A).toMeasure ≤
      ENNReal.ofReal (40*(2*p+2)*((H0:ℝ)-27)^j.val*(3:ℝ)^(4*A.gamma*((H0:ℝ)-27))) := by
  have hγ : 0 ≤ A.gamma := A.shellPrefix.gamma_pos.le
  have hHr := (selected_candidate_mem H0 H).mp hHC
  have hsource := physical_height_weighted_wave_Lp A h hA Q N hQN H0 hH hpast a c weights hw layer j H hHr.1 p hp
  have hHreal : (333:ℝ) ≤ H := by exact_mod_cast (le_trans hH hHr.1)
  have h0real : (333:ℝ) ≤ H0 := by exact_mod_cast hH
  have hupper : (H:ℝ) ≤ (H0:ℝ)+11 := by exact_mod_cast hHr.2
  have hz : (0:ℝ) ≤ (H:ℝ)-38 := by linarith only [hHreal]
  have hz' : (0:ℝ) ≤ (H0:ℝ)-27 := by linarith only [h0real]
  have hzz : (H:ℝ)-38 ≤ (H0:ℝ)-27 := by linarith only [hupper]
  have hpow := pow_le_pow_left₀ hz hzz j.val
  have hclock := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3)
    (mul_le_mul_of_nonneg_left hzz (show 0 ≤ 4*A.gamma by positivity))
  have hcoef : 40*(p+2) ≤ 40*(2*p+2) := by linarith only [hp]
  have hprod := mul_le_mul hcoef hpow (pow_nonneg hz j.val) (by positivity : 0 ≤ 40*(2*p+2))
  have hprod' := mul_le_mul hprod hclock
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 3) _) (mul_nonneg (by positivity) (pow_nonneg hz' _))
  exact hsource.trans (ENNReal.ofReal_le_ofReal hprod')


end
end ASDExplicitGamma.Inverse
