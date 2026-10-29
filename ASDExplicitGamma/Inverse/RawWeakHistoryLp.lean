module

public import ASDExplicitGamma.Inverse.RawWeakHistory
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-! The weak history as a convergent series in the actual probability `L²` space. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The weak history formed in `L²`, so its definition includes the norm limit. -/
def rawWeakHistoryLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : ℕ → Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (1 - Scalar.inverseHistoryDiscount) •
    ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j • T j

/-- Build the weak-history `L²` element directly from its source functions. -/
noncomputable def rawWeakHistoryOfMemLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : ℕ → Ω → ℝ)
    (hT : ∀ j, MemLp (T j) 2 μ) : Lp ℝ 2 μ :=
  rawWeakHistoryLp μ (fun j => (hT j).toLp (T j))

/-- The exact `L²` triangle estimate for the normalization. -/
theorem raw_weak_history_lpNorm_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (T : ℕ → Lp ℝ 2 μ)
    (hT : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j * ‖T j‖)) :
    ‖rawWeakHistoryLp μ T‖ ≤
      (1 - Scalar.inverseHistoryDiscount) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * ‖T j‖ := by
  let α := Scalar.inverseHistoryDiscount
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hα1 : α < 1 := hα.2
  have hSeries : Summable (fun j : ℕ => ‖α ^ j • T j‖) := by
    apply hT.congr
    intro j
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hα0 j)]
  have hNormSeries :
      (∑' j : ℕ, ‖α ^ j • T j‖) =
        ∑' j : ℕ, α ^ j * ‖T j‖ := by
    apply tsum_congr
    intro j
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hα0 j)]
  have hTsum := norm_tsum_le_tsum_norm hSeries
  have hFactor : 0 ≤ 1 - α := sub_nonneg.mpr hα1.le
  calc
    ‖rawWeakHistoryLp μ T‖ =
        (1 - α) * ‖∑' j : ℕ, α ^ j • T j‖ := by
      rw [rawWeakHistoryLp, show Scalar.inverseHistoryDiscount = α by rfl,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hFactor]
    _ ≤ (1 - α) * ∑' j : ℕ, ‖α ^ j • T j‖ :=
      mul_le_mul_of_nonneg_left hTsum hFactor
    _ = (1 - α) * ∑' j : ℕ, α ^ j * ‖T j‖ := by rw [hNormSeries]
    _ = (1 - Scalar.inverseHistoryDiscount) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * ‖T j‖ := by rfl

/-- A summable depthwise envelope for the L² norms gives the corresponding
explicit bound on the normalized weak-history norm. -/
theorem raw_weak_history_lpNorm_le_of_envelope {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : ℕ → Lp ℝ 2 μ) (U : ℕ → ℝ)
    (hU : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j * U j))
    (hbound : ∀ j, ‖T j‖ ≤ U j) :
    ‖rawWeakHistoryLp μ T‖ ≤
      (1 - Scalar.inverseHistoryDiscount) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * U j := by
  have hα := Scalar.inverse_history_discount_range
  have hterms (j : ℕ) : Scalar.inverseHistoryDiscount ^ j * ‖T j‖ ≤
      Scalar.inverseHistoryDiscount ^ j * U j :=
    mul_le_mul_of_nonneg_left (hbound j) (pow_nonneg hα.1.le j)
  have hT : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j * ‖T j‖) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (pow_nonneg hα.1.le j) (norm_nonneg _)) hterms hU
  have hsum := hT.tsum_le_tsum hterms hU
  have hfactor : 0 ≤ 1 - Scalar.inverseHistoryDiscount :=
    sub_nonneg.mpr hα.2.le
  calc
    ‖rawWeakHistoryLp μ T‖ ≤
        (1 - Scalar.inverseHistoryDiscount) *
          ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * ‖T j‖ :=
      raw_weak_history_lpNorm_le μ T hT
    _ ≤ (1 - Scalar.inverseHistoryDiscount) *
          ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * U j :=
      mul_le_mul_of_nonneg_left hsum hfactor

/-- Envelope form for a weak history assembled from the source functions. -/
theorem raw_weak_history_of_memLp_lpNorm_le_of_envelope {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (T : ℕ → Ω → ℝ)
    (hT : ∀ j, MemLp (T j) 2 μ) (U : ℕ → ℝ)
    (hU : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j * U j))
    (hbound : ∀ j, ‖(hT j).toLp (T j)‖ ≤ U j) :
    ‖rawWeakHistoryOfMemLp μ T hT‖ ≤
      (1 - Scalar.inverseHistoryDiscount) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ j * U j := by
  exact raw_weak_history_lpNorm_le_of_envelope μ
    (fun j => (hT j).toLp (T j)) U hU hbound

end
end ASDExplicitGamma.Inverse
