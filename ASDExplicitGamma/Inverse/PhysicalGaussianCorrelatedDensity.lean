module

public import ASDExplicitGamma.Inverse.PhysicalGaussianResetWave
public import ASDExplicitGamma.Inverse.StoppedResetDensityFields
public import ASDExplicitGamma.Inverse.StoppedDensitySumNorm
public import ASDExplicitGamma.Inverse.StoppedDensityResolution

/-! Exact correlated wave/density Holder payment. The density keeps order p;
ordinary wave moments use 2p, hence the underlying Gaussian orders 2p/4p.
The actual reset corollary discharges both norm inputs from the model. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Source (7.7), on an arbitrary joint law with no independence premise. -/
theorem physical_wave_sqrt_density_holder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W Y : Ω → ℝ) (hW : AEStronglyMeasurable W μ)
    (hY : AEStronglyMeasurable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (p C : ℝ) (hp : 0 < p) (hC : 0 ≤ C)
    (hb : eLpNorm Y (ENNReal.ofReal p) μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun ω => W ω*Real.sqrt (Y ω)) (ENNReal.ofReal p) μ ≤
      eLpNorm W (ENNReal.ofReal (2*p)) μ*ENNReal.ofReal (Real.sqrt C) := by
  let physicalWaveDensityHolderTriple : ENNReal.HolderTriple (ENNReal.ofReal (2*p))
      (ENNReal.ofReal (2*p)) (ENNReal.ofReal p) := by
    constructor
    rw [← ENNReal.ofReal_inv_of_pos (mul_pos (by norm_num) hp),
      ← ENNReal.ofReal_inv_of_pos hp,← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    field_simp
    ring
  have hs := density_sqrt_Lp μ Y hY hY0 p C hp hC hb
  have hsm : MemLp (fun ω => Real.sqrt (Y ω)) (ENNReal.ofReal (2*p)) μ :=
    memLp_iff.mpr (hs.trans_lt ENNReal.ofReal_lt_top)
  have hh := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal (2*p))
    (q := ENNReal.ofReal (2*p)) (r := ENNReal.ofReal p) hW hsm.aestronglyMeasurable
  have he : (W • fun ω => Real.sqrt (Y ω))=(fun ω => W ω*Real.sqrt (Y ω)) := by funext ω; rfl
  rw [he] at hh
  exact hh.trans (mul_le_mul_right hs _)

end
end ASDExplicitGamma.Inverse
