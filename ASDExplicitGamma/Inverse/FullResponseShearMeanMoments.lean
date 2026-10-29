module

public import ASDExplicitGamma.Inverse.AssemblyShearSign

/-! Scalar moments for the actual identity-layer shear means. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Variational
open scoped ENNReal

noncomputable section

/-- The actual normalized scalar shear mean is ambient measurable. -/
theorem physical_shear_mean_measurable
    (M : ABKModel 2) (j n N : ℤ) (a c : ℝ) (weights : ℤ → ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      physicalMissingWaveAverage M j n N a c weights ω/(Annealed.sigmaBar M j : ℝ)) := by
  have hR := assembly_physical_shear_measurable M j n N a c weights
  have he := (measurable_pi_apply (Sum.inl (1:Fin 2))).comp
    ((measurable_pi_apply (Sum.inr (0:Fin 2))).comp hR)
  convert he using 1
  funext ω
  change physicalMissingWaveAverage M j n N a c weights ω/(Annealed.sigmaBar M j : ℝ) =
    assemblyPhysicalShearMatrix M j n N a c weights ω (Sum.inr 0) (Sum.inl 1)
  simp [assemblyPhysicalShearMatrix, constantSkewMatrix, toFullBlockMat,
    Response.responsePlanarJ]

/-- Squared local shear means satisfy the source scalar-wave envelope on
every deterministic observation square. Only the actual old label is used
for the native input; the terminal cutoff may be below the root scale. -/
theorem physical_shear_mean_square_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (j n N : ℤ) (hstrict : j < N) (hstate : nativeInductionState M h j)
    (a c : ℝ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1)
    (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
      (physicalMissingWaveAverage M j n N a c weights ω/(Annealed.sigmaBar M j : ℝ))^2)
      (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (20*(p+2)*(M.gamma*(N-j:ℝ)*(3:ℝ)^(2*M.gamma*(N-j:ℝ)))) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ := (Annealed.sigmaBar M j : ℝ)
  let avg := physicalMissingWaveAverage M j n N a c weights
  let x := fun ω : Cutoff.CutoffSample 2 => avg ω/σ
  have havg : MemLp avg (ENNReal.ofReal (2*p)) μ :=
    missingWave_model_average_memLp hstrict.le hstrict M h hM a c ((3:ℝ)^n)
      (by positivity) weights hp
  have hx : MemLp x (ENNReal.ofReal (2*p)) μ := by
    have he : x = σ⁻¹ • avg := by
      funext ω
      simp only [x, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [he]
    exact havg.const_smul _
  have hpow : eLpNorm (fun ω => x ω^2) (ENNReal.ofReal p) μ =
      eLpNorm x (ENNReal.ofReal (2*p)) μ ^ 2 := by
    have hh := eLpNorm_norm_rpow (p := ENNReal.ofReal p) x hx.aestronglyMeasurable
      (by norm_num : (0:ℝ)<2)
    have he : ENNReal.ofReal p*ENNReal.ofReal 2 = ENNReal.ofReal (2*p) := by
      rw [← ENNReal.ofReal_mul (by linarith only [hp] : (0:ℝ)≤p)]
      congr 1
      ring
    rw [he] at hh
    simpa only [Real.norm_eq_abs, Real.rpow_ofNat, sq_abs, ENNReal.rpow_two] using hh
  have htop : eLpNorm (fun ω => x ω^2) (ENNReal.ofReal p) μ ≠ ∞ := by
    rw [hpow]
    exact ENNReal.pow_ne_top hx.eLpNorm_ne_top
  rw [← ENNReal.ofReal_toReal htop]
  apply ENNReal.ofReal_le_ofReal
  rw [hpow, ENNReal.toReal_pow]
  have hm := missingWave_model_average_normalized_lpNorm_sq_le hstrict.le hstrict
    M h hM hstate a c ((3:ℝ)^n) (by positivity) weights hw hp
  have hgap : (0:ℝ) ≤ (N-j:ℝ) := by exact_mod_cast sub_nonneg.mpr hstrict.le
  have hclock : 0 ≤ M.gamma*(N-j:ℝ)*(3:ℝ)^(2*M.gamma*(N-j:ℝ)) := by
    exact mul_nonneg (mul_nonneg M.shellPrefix.gamma_pos.le hgap) (by positivity)
  apply hm.trans
  have hc : (2*p+2)*9 ≤ 20*(p+2) := by linarith only [hp]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_right hc hclock

end
end ASDExplicitGamma.Inverse
