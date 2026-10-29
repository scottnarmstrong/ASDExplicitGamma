module

public import ASDExplicitGamma.Scalar.RefRough7

/-! `L^{128/127}` norm of `(c B* + 1)⁴` and the pathwise/`L^q` rough bound of the full defect
budget with the explicit constant `R = A² ((44/25) b + 1)⁴`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators ENNReal

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem eLpNorm_pow4 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → ℝ) (hBm : Measurable B) (hB0 : ∀ ω, 0 ≤ B ω) (b c : ℝ) (hb0 : 0 ≤ b) (hc : 0 ≤ c)
    (hb : eLpNorm B 128 μ ≤ ENNReal.ofReal b) :
    eLpNorm (fun ω => (c * B ω + 1) ^ 4) (ENNReal.ofReal (128 / 127)) μ ≤
      ENNReal.ofReal ((c * b + 1) ^ 4) := by
  set g : Ω → ℝ := fun ω => c * B ω + 1 with hg
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by simp only [hg]; have := hB0 ω; positivity
  have hgm : AEStronglyMeasurable g μ := ((hBm.const_mul c).add_const 1).aestronglyMeasurable
  have hpow : (fun ω => (c * B ω + 1) ^ 4) = fun ω => ‖g ω‖ ^ (4 : ℝ) := by
    funext ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 ω), ← Real.rpow_natCast]
    norm_num [hg]
  rw [hpow, eLpNorm_norm_rpow g hgm (by norm_num)]
  have hr : ENNReal.ofReal (128 / 127) * ENNReal.ofReal 4 = ENNReal.ofReal (512 / 127) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
  rw [hr]
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (512 / 127) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hle128 : ENNReal.ofReal (512 / 127) ≤ 128 := by
    rw [show (128 : ℝ≥0∞) = ENNReal.ofReal 128 by simp]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hgsum : g = (c • B) + (fun _ : Ω => (1 : ℝ)) := by
    funext ω; simp [hg]
  have h2 : eLpNorm g (ENNReal.ofReal (512 / 127)) μ ≤ ENNReal.ofReal (c * b + 1) := by
    rw [hgsum]
    refine (eLpNorm_add_le h1).trans ?_
    have hc1 : eLpNorm (c • B) (ENNReal.ofReal (512 / 127)) μ ≤ ENNReal.ofReal (c * b) := by
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hc, ENNReal.ofReal_mul hc]
      gcongr
      exact (eLpNorm_le_eLpNorm_of_exponent_le hle128).trans hb
    have hc2 : eLpNorm (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal (512 / 127)) μ ≤ 1 := by
      rw [eLpNorm_const _ (by simp) (IsProbabilityMeasure.ne_zero μ)]
      simp
    calc _ ≤ ENNReal.ofReal (c * b) + 1 := add_le_add hc1 hc2
      _ = ENNReal.ofReal (c * b + 1) := by
        rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp
  calc eLpNorm g (ENNReal.ofReal (512 / 127)) μ ^ (4 : ℝ)
      ≤ (ENNReal.ofReal (c * b + 1)) ^ (4 : ℝ) := ENNReal.rpow_le_rpow h2 (by norm_num)
    _ = ENNReal.ofReal ((c * b + 1) ^ 4) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      norm_num

end

end ASDExplicitGamma.Scalar
