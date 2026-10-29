module

public import ASDExplicitGamma.Main.ThetaGeneratorHotObsVl2
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationPointwise
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsSplit
public import ASDExplicitGamma.Gaussian.RioTwoSum

/-! Node MA-E-OSCILLATION for the hot-patched trial at the observer root
`Q' = originCube 2 (m + hobs)` (`1 ≤ hobs ≤ 40`): the actual-law expectation of the oscillatory
C-group is at most `2 d q`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response

noncomputable section

/-- Cauchy-Schwarz for `√u · S` with `u` integrable and `S` in `L²`. -/
theorem hot_integral_sqrt_mul_le_Th {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u S : Ω → ℝ) (hu0 : ∀ ω, 0 ≤ u ω) (hu : Integrable u μ) (hS : MemLp S 2 μ)
    (hS0 : ∀ ω, 0 ≤ S ω) :
    Integrable (fun ω => Real.sqrt (u ω) * S ω) μ ∧
      (∫ ω, Real.sqrt (u ω) * S ω ∂μ) ≤
        Real.sqrt (∫ ω, u ω ∂μ) * Real.sqrt (∫ ω, S ω ^ 2 ∂μ) := by
  have hsq : MemLp (fun ω => Real.sqrt (u ω)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hu.aestronglyMeasurable)).2
      (hu.congr (Filter.Eventually.of_forall fun ω => (Real.sq_sqrt (hu0 ω)).symm))
  refine ⟨hsq.integrable_mul hS, ?_⟩
  have hf2 : MemLp (fun ω => Real.sqrt (u ω)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hsq
  have hg2 : MemLp S (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa only [ENNReal.ofReal_ofNat] using hS
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by constructor <;> norm_num)
    (Filter.Eventually.of_forall fun ω => Real.sqrt_nonneg (u ω))
    (Filter.Eventually.of_forall hS0) hf2 hg2
  norm_num only [Real.rpow_ofNat] at hh
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
  have e1 : (∫ ω, Real.sqrt (u ω) ^ 2 ∂μ) = ∫ ω, u ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => Real.sq_sqrt (hu0 ω))
  rw [e1] at hh
  exact hh

theorem hot_integral_sq_le_of_lpNorm_Th {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : Ω → ℝ) (hS : MemLp S 2 μ) (q : ℝ) (hq : lpNorm S 2 μ ≤ q) :
    Real.sqrt (∫ ω, S ω ^ 2 ∂μ) ≤ q := by
  rw [← ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hS]
  rw [Real.sqrt_sq (lpNorm_nonneg (f := S) (p := 2) (μ := μ))]
  exact hq

end

end ASDExplicitGamma.Main
