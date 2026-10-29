module

public import ASDExplicitGamma.Inverse.PhysicalGaussianMissingWave

/-! Actual true-frame shear amplitudes, including finite extended Lp control. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Actual physical scalar average of the later shell band on the source square. -/
def physicalMissingWaveAverage (_A : ABKModel 2) (j n N : ℤ) (a c : ℝ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  q3SpatialAverageCLM (by rw [spatialVolume_square_real (R := (3:ℝ)^n) (by positivity)]; positivity)
    (wholeRootModelBand (a := a) (b := a+(3:ℝ)^n) (c := c) (d := c+(3:ℝ)^n) j N weights ω)

/-- Actual physical cube-average shear, in its own earlier-label true frame. -/
def physicalMissingWaveShear (A : ABKModel 2) (j n N : ℤ) (a c : ℝ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) : HilbertBlockVec 2 →L[ℝ] HilbertBlockVec 2 :=
  missingWaveShearOperator (Annealed.sigmaBar A j) (physicalMissingWaveAverage A j n N a c weights ω)

/-- Finite shear norm from finite scalar-average moments. -/
theorem physical_shear_sq_memLp_of_average_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (avg : Ω → ℝ) (σ p : ℝ)
    (havg : MemLp avg (ENNReal.ofReal (2*p)) μ) :
    MemLp (fun ω => ‖missingWaveShearOperator σ (avg ω)‖^2) (ENNReal.ofReal p) μ := by
  let x : Ω → ℝ := fun ω => avg ω/σ
  have hx : MemLp x (ENNReal.ofReal (2*p)) μ := by
    have he : x = σ⁻¹ • avg := by
      funext ω
      change avg ω/σ = σ⁻¹*avg ω
      rw [div_eq_mul_inv]
      ring
    rw [he]
    exact havg.const_smul _
  have hdiv : ENNReal.ofReal (2*p)/ENNReal.ofReal 2 = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hx2 : MemLp (fun ω => x ω^2) (ENNReal.ofReal p) μ := by
    convert hx.norm_rpow_div (ENNReal.ofReal 2) using 1
    · funext ω
      simp only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2),Real.rpow_ofNat,Real.norm_eq_abs,sq_abs]
    · exact hdiv.symm
  have hRHS : MemLp (fun ω => 2+2*x ω^2) (ENNReal.ofReal p) μ :=
    (memLp_const (2 : ℝ)).add (hx2.const_smul (2 : ℝ))
  have hcont : Continuous (fun η : ℝ => ‖missingWaveShearOperator σ η‖^2) := by
    unfold missingWaveShearOperator
    exact (continuous_const.add (continuous_id.smul continuous_const)).norm.pow 2
  have hm : AEStronglyMeasurable (fun ω => ‖missingWaveShearOperator σ (avg ω)‖^2) μ :=
    hcont.comp_aestronglyMeasurable havg.aestronglyMeasurable
  apply hRHS.mono' hm
  filter_upwards with ω
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact missingWaveShearOperator_norm_sq_le σ (avg ω)

/-- Finite extended norm is proved before the actual shear's toReal estimate is consumed. -/
theorem physical_missing_wave_shear_sq_memLp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (j n N : ℤ) (hstrict : j < N) (a c : ℝ) (weights : ℤ → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    MemLp (fun ω => ‖physicalMissingWaveShear A j n N a c weights ω‖^2) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw A).toMeasure := by
  exact physical_shear_sq_memLp_of_average_memLp (Cutoff.cutoffSampleLaw A).toMeasure
    (physicalMissingWaveAverage A j n N a c weights) (Annealed.sigmaBar A j) p
    (missingWave_model_average_memLp hstrict.le hstrict A h hA a c ((3:ℝ)^n) (by positivity) weights hp)

/-- Honest extended Lp shear bound; its finite-norm proof is internal. -/
theorem physical_missing_wave_shear_sq_Lp (A : ABKModel 2) (h : ℝ) (hA : PlanarQ3Gaussian A h)
    (j n N : ℤ) (hstrict : j < N) (hstate : nativeInductionState A h j)
    (a c : ℝ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc j N, 0 ≤ weights k ∧ weights k ≤ 1)
    (p : ℝ) (hp : 1 ≤ p) :
    eLpNorm (fun ω => ‖physicalMissingWaveShear A j n N a c weights ω‖^2) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw A).toMeasure ≤
      ENNReal.ofReal (2+80*(p+2)*(A.gamma*(N-j:ℝ)*(3:ℝ)^(2*A.gamma*(N-j:ℝ)))) := by
  have hm := physical_missing_wave_shear_sq_memLp A h hA j n N hstrict a c weights p hp
  rw [← ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal (missingWave_model_shear_lpNorm_bound hstrict.le hstrict A h hA
    hstate a c ((3:ℝ)^n) (by positivity) weights hw hp)

end
end ASDExplicitGamma.Inverse
