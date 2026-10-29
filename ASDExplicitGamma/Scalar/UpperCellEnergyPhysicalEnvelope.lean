module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalBandVariance
public import ASDExplicitGamma.Scalar.UpperCellEnergyEnvelopeScaling
public import ASDExplicitGamma.Scalar.UpperCellEnergyEndpointProfiles

/-! The literal normalized full-band sensitivity envelope satisfies the certified f cap. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Gaussian Model MeasureTheory
open Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Full-band derivative envelope on the physical depth-fourteen square. -/
def upperCellPhysicalEnvelope (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (c : Vec 2) : Cutoff.CutoffSample 2 → ℝ :=
  upperCellBandEnvelope (upperCellPhysicalBandLabel n height)
    (fun _ => (Annealed.sigmaBar M n : ℝ)⁻¹) c
    ((3:ℝ)^(n-14)) ((3:ℝ)^(n-14)) (((3:ℝ)^(n-14))^2)

/-- Physical covariance scaling bounds both actual envelope profiles. -/
theorem upper_cell_physical_envelope_profiles
    (M : ABKModel 2) (h : ℝ) (n : ℤ) (height : ℕ) (hg : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h n) :
    upperCellBandEnvelopeMean M h (upperCellPhysicalBandLabel n height)
      (fun _ => (Annealed.sigmaBar M n : ℝ)⁻¹)
      ((3:ℝ)^(n-14)) ((3:ℝ)^(n-14)) (((3:ℝ)^(n-14))^2) ≤
      (Real.sqrt M.gamma*(3:ℝ)^(-14:ℤ))*waveMeanAt ((3:ℝ)^(-14:ℤ)) ∧
    upperCellBandEnvelopeCM M h (upperCellPhysicalBandLabel n height)
      (fun _ => (Annealed.sigmaBar M n : ℝ)⁻¹)
      ((3:ℝ)^(n-14)) (((3:ℝ)^(n-14))^2) ≤
      (Real.sqrt M.gamma*(3:ℝ)^(-14:ℤ))*waveEllAt ((3:ℝ)^(-14:ℤ)) := by
  have h1 := upper_cell_physical_band_root_variance_le M h n hg hstate 1 height (by omega)
  have h2 := upper_cell_physical_band_root_variance_le M h n hg hstate 2 height (by omega)
  have h3 := upper_cell_physical_band_root_variance_le M h n hg hstate 3 height (by omega)
  simp only [pow_one] at h1
  have h2' : ((3:ℝ)^(n-14))^2 * Real.sqrt (upperCellBandVariance M h
      (upperCellPhysicalBandLabel n height) (fun _ => (Annealed.sigmaBar M n : ℝ)⁻¹) 2) ≤
      (Real.sqrt M.gamma*(3:ℝ)^(-14:ℤ))*(3:ℝ)^(-14:ℤ) := by
    convert h2 using 1
    ring
  have h3' : ((3:ℝ)^(n-14))^3 * Real.sqrt (upperCellBandVariance M h
      (upperCellPhysicalBandLabel n height) (fun _ => (Annealed.sigmaBar M n : ℝ)⁻¹) 3) ≤
      (Real.sqrt M.gamma*(3:ℝ)^(-14:ℤ))*((3:ℝ)^(-14:ℤ))^2 := by
    convert h3 using 1
    ring
  exact ⟨upper_cell_band_envelope_mean_scaling M h _ _ _ _ _ h1 h2' h3',
    upper_cell_band_envelope_cm_scaling M h _ _ _ _ _ h1 h2'⟩

/-- The actual physical envelope belongs to L6 and satisfies the exact f profile
used in the endpoint error certificate. The completed state is only the OLD state. -/
theorem upper_cell_physical_envelope_L6
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (height : ℕ) (hhgt : 0 < height) (c : Vec 2) (hg : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h n) :
    MemLp (upperCellPhysicalEnvelope M n height c) 6 (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (eLpNorm (upperCellPhysicalEnvelope M n height c) 6
      (Cutoff.cutoffSampleLaw M).toMeasure).toReal ≤ upperCellFProfile M.gamma := by
  let k := upperCellPhysicalBandLabel n height
  let w := fun _ : Fin height => (Annealed.sigmaBar M n : ℝ)⁻¹
  let R := (3:ℝ)^(n-14)
  let delta := (3:ℝ)^(-14:ℤ)
  let t := Real.sqrt M.gamma * delta
  have hR : 0 < R := by dsimp only [R]; positivity
  have hV := upper_cell_physical_band_variance_pos M h hM.1 n height
  have hL : 0 < upperCellBandEnvelopeCM M h k w R (R^2) := by
    have he1 : 0 < waveEll1 := by norm_num [waveEll1,waveR1]
    exact add_pos_of_pos_of_nonneg
      (mul_pos hR (Real.sqrt_pos.mpr (mul_pos (sq_pos_of_pos he1) (hV 1 hhgt))))
      (mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _))
  have hm := upper_cell_band_envelope_moment M h hM k
    (upper_cell_physical_band_label_injective n height) w c R R (R^2)
    hR hR.le (sq_nonneg _) (hV 2 hhgt) (hV 3 hhgt) hL 6 (by norm_num)
  norm_num only [ENNReal.ofReal_ofNat] at hm
  refine ⟨hm.1, ?_⟩
  have hp := upper_cell_physical_envelope_profiles M h n height hg hstate
  have hmean0 : 0 ≤ upperCellBandEnvelopeMean M h k w R R (R^2) := by
    have hi := upper_cell_band_envelope_mean M h hM k
      (upper_cell_physical_band_label_injective n height) w c R R (R^2)
      hR hR.le (sq_nonneg _) (hV 2 hhgt) (hV 3 hhgt)
    exact (integral_nonneg (upper_cell_band_envelope_nonneg k w c R R (R^2)
      hR.le (sq_nonneg _))).trans hi.2
  have hmsq := pow_le_pow_left₀ hmean0 hp.1 2
  have hlsq := pow_le_pow_left₀ hL.le hp.2 2
  have hc := mul_le_mul_of_nonneg_left upper_cell_envelope_six_constant (sq_nonneg t)
  have htotal : (eLpNorm (upperCellPhysicalEnvelope M n height c) 6
      (Cutoff.cutoffSampleLaw M).toMeasure).toReal^2 ≤ (64*t)^2 := by
    calc
      _ ≤ 2*(upperCellBandEnvelopeMean M h k w R R (R^2))^2+
          12*(upperCellBandEnvelopeCM M h k w R (R^2))^2 := hm.2
      _ ≤ 2*(t*waveMeanAt delta)^2+12*(t*waveEllAt delta)^2 :=
        add_le_add (mul_le_mul_of_nonneg_left hmsq (by norm_num))
          (mul_le_mul_of_nonneg_left hlsq (by norm_num))
      _ = t^2*(2*(waveMeanAt delta)^2+12*(waveEllAt delta)^2) := by ring
      _ ≤ t^2*64^2 := hc
      _ = (64*t)^2 := by ring
  have hf : upperCellFProfile M.gamma = 64*t := by
    dsimp only [upperCellFProfile,t,delta]
    norm_num only [zpow_neg, zpow_ofNat]
    ring
  rw [hf]
  exact (sq_le_sq₀ ENNReal.toReal_nonneg (by dsimp only [t,delta]; positivity)).mp htotal


/-- Extended-valued formulation of the actual f cap, retaining finiteness. -/
theorem upper_cell_physical_envelope_eLpNorm_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (n : ℤ)
    (height : ℕ) (hhgt : 0 < height) (c : Vec 2) (hg : M.gamma ≤ gammaZero)
    (hstate : nativeInductionState M h n) :
    eLpNorm (upperCellPhysicalEnvelope M n height c) 6
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (upperCellFProfile M.gamma) := by
  have hh := upper_cell_physical_envelope_L6 M h hM n height hhgt c hg hstate
  rw [← ENNReal.ofReal_toReal (ne_of_lt hh.1)]
  exact ENNReal.ofReal_le_ofReal hh.2

end
end ASDExplicitGamma.Scalar
