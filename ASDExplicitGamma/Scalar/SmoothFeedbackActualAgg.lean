/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackActualFields
public import ASDExplicitGamma.Scalar.SmoothFeedbackConsumerArith

/-! Integrability and Hölder-range bounds of the actual smooth-feedback charges
from the `L²` moment of the cell histories `M_U`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Main ASDExplicitGamma.Inverse
open Algsuperdiff.Section3
open scoped BigOperators ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

/-- The multiplier moment bound `m_*` of SC-ANALYTIC-BOUND-M. -/
def mStar' (M : ABKModel 2) : ℝ := mainM0 (mainEnvelopeH (theta M) M.gamma 0)

theorem mStar_nonneg (M : ABKModel 2) : 0 ≤ mStar' M := by
  unfold mStar' mainM0
  have := mainEnvelopeH_nonneg (theta M) M.gamma 0
  have := Real.sqrt_nonneg (2 * mainEnvelopeH (theta M) M.gamma 0)
  linarith

theorem eLpNorm_const_mul_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {e K : ℝ} (hK : 0 ≤ K)
    (h : eLpNorm f 2 μ ≤ ENNReal.ofReal e) :
    eLpNorm (fun x => K * f x) 2 μ ≤ ENNReal.ofReal (K * e) := by
  have : (fun x => K * f x) = K • f := by funext x; simp
  rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal hK, ENNReal.ofReal_mul hK]
  gcongr

/-- `L²` bound of the cell history, by translation to the origin cell. -/
theorem cellHist_L2 (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (Q : TriadicCube 2) (hQ : Q.scale = m + 129) (U : OldSignedCellIndex Q 134) :
    eLpNorm (fun ω => cellResponseHistory M m U.val ω) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (mStar' M) := by
  apply cell_history_L2 M h hM hγ m hpast U.val
  have := scale_eq_sub_of_mem_descendantsAtDepth U.property
  rw [this, hQ]
  push_cast
  ring

theorem cellAverage_le_of_le (Q : TriadicCube 2) (depth : ℕ)
    {T c Mf : OldSignedCellIndex Q depth → ℝ} (hc : ∀ U, 0 ≤ c U)
    (hcell : ∀ U, T U ≤ c U * Mf U) :
    oldSignedCellAverage Q depth T ≤
      ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * ∑ U, c U * Mf U := by
  unfold oldSignedCellAverage
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun U _ => hcell U)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Aggregation of the cell histories. -/
theorem agg_charge {ι : Type*} (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ) (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (Q : TriadicCube 2) (hQ : Q.scale = m + 129) (S : Finset ι)
    (c : ι → OldSignedCellIndex Q 134 → ℝ) (hc0 : ∀ i U, 0 ≤ c i U)
    {K : ℝ} (hK : 0 ≤ K) {Z : Cutoff.CutoffSample 2 → ℝ} (hZm : Measurable Z)
    (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hZle : ∀ ω, Z ω ≤ ∑ i ∈ S, ((descendantsAtDepth Q 134).card : ℝ)⁻¹ *
      ∑ U, c i U * (K * cellResponseHistory M m U.val ω)) :
    Integrable Z (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω, Z ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (K * mStar' M) * ∑ i ∈ S, ((descendantsAtDepth Q 134).card : ℝ)⁻¹ * ∑ U, c i U ∧
    eLpNorm Z (ENNReal.ofReal (128 / 127)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((K * mStar' M) *
        ∑ i ∈ S, ((descendantsAtDepth Q 134).card : ℝ)⁻¹ * ∑ U, c i U) :=
  agg_bounds S _ (inv_nonneg.mpr (Nat.cast_nonneg _)) c hc0
    (fun U ω => K * cellResponseHistory M m U.val ω)
    (fun U ω => mul_nonneg hK (cellResponseHistory_nonneg M m U.val ω))
    (mul_nonneg hK (mStar_nonneg M))
    (fun U => eLpNorm_const_mul_le hK (cellHist_L2 M h hM hγ m hpast Q hQ U))
    Z hZm hZ0 hZle

end

end ASDExplicitGamma.Scalar
