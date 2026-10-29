module

public import ASDExplicitGamma.Main.ThetaGeneratorELinearXiHalf
public import ASDExplicitGamma.Main.ELinearPathwise
public import ASDExplicitGamma.Main.ELinearCorrector
public import ASDExplicitGamma.Main.ELinearKappa
public import ASDExplicitGamma.Native.OldSignedSqrtExpectation

/-! Actual-law expectation of the leading part of a depth-five cell term of
the `L` group: mean/oscillation terms and the deterministic part of the
negative-flat feedback. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- Square-root contraction for a.e. nonnegative integrable functions. -/
theorem main_sqrt_expectation_ae_Th {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) :
    Integrable (fun ω => Real.sqrt (f ω)) μ ∧
      (∫ ω, Real.sqrt (f ω) ∂μ) ≤ Real.sqrt (∫ ω, f ω ∂μ) := by
  let g : Ω → ℝ := fun ω => max (f ω) 0
  have hfg : f =ᵐ[μ] g := by
    filter_upwards [hn] with ω hω
    have hω' : 0 ≤ f ω := hω
    simp [g, hω']
  have hg : Integrable g μ := hf.congr hfg
  obtain ⟨h1, h2⟩ := old_signed_sqrt_expectation μ g hg (fun ω => le_max_right _ _)
  have hs : (fun ω => Real.sqrt (f ω)) =ᵐ[μ] (fun ω => Real.sqrt (g ω)) := by
    filter_upwards [hfg] with ω hω
    rw [hω]
  refine ⟨h1.congr hs.symm, ?_⟩
  rw [integral_congr_ae hs]
  exact h2.trans_eq (by rw [integral_congr_ae hfg])

/-- `L¹` mean bounded by the `L²` norm on a probability space. -/
theorem main_integral_le_lpNorm_two_Th {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    ∫ x, f x ∂μ ≤ lpNorm f 2 μ := by
  have h1 : MemLp f 1 μ := hf.mono_exponent (by norm_num)
  have hle : eLpNorm f 1 μ ≤ eLpNorm f 2 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have : ∫ x, f x ∂μ ≤ ∫ x, ‖f x‖ ∂μ :=
    integral_mono (memLp_one_iff_integrable.mp h1) (memLp_one_iff_integrable.mp h1).norm
      (fun x => (le_abs_self _).trans_eq (Real.norm_eq_abs _).symm)
  refine this.trans ?_
  have h2 : ∫ x, ‖f x‖ ∂μ = (eLpNorm f 1 μ).toReal := by
    rw [integral_norm_eq_lintegral_enorm h1.aestronglyMeasurable, eLpNorm_one_eq_lintegral_enorm]
    exact h1.aestronglyMeasurable
  rw [h2]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top hle

end

end ASDExplicitGamma.Main
