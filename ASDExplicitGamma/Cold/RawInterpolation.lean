module

public import ASDExplicitGamma.Cold.ColdInterpolationTable

/-! # Uncentered trace interpolation for the source matrix variance charge -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Nonnegative trace interpolation also bounds the raw L2 norm used in the spectral charge. -/
theorem raw_l2_le_interpolated_caps {Ω : Type*} [MeasurableSpace Ω]
    (μprob : Measure Ω) [IsProbabilityMeasure μprob] {X : Ω → ℝ} {D M : ℝ}
    (hX : MemLp X 20 μprob) (hn : ∀ᵐ ω ∂μprob, 0 ≤ X ω)
    (hmean : (∫ ω, X ω ∂μprob) ≤ D) (hcap : lpNorm X 20 μprob ≤ M) :
    lpNorm X 2 μprob ≤ D^(9/19:ℝ)*M^(10/19:ℝ) := by
  have h1 : lpNorm X 1 μprob ≤ D := by
    rw [lpNorm_one_eq_integral_norm hX.aestronglyMeasurable]
    exact (integral_congr_ae (hn.mono (fun ω hω => Real.norm_of_nonneg hω))).trans_le hmean
  exact (lpNorm_two_le_one_twenty μprob hX).trans (mul_le_mul
    (Real.rpow_le_rpow lpNorm_nonneg h1 (by norm_num))
    (Real.rpow_le_rpow lpNorm_nonneg hcap (by norm_num))
    (Real.rpow_nonneg lpNorm_nonneg _) (Real.rpow_nonneg (lpNorm_nonneg.trans h1) _))

/-- The producing nineteenth-power certificate bounds the raw native trace norm as well. -/
theorem cold_raw_interpolation_table_cap {Ω : Type*} [MeasurableSpace Ω] {μprob : Measure Ω}
    [IsProbabilityMeasure μprob] {X : Ω → ℝ} {θ : ℝ} (hθ : 0 ≤ θ) {k : ℕ} (hk : k ≤ 126)
    (hX : MemLp X 20 μprob) (hn : ∀ᵐ ω ∂μprob, 0 ≤ X ω)
    (hmean : (∫ ω, X ω ∂μprob) ≤ θ*(coldMeanAt k:ℝ))
    (hmoment : lpNorm X 20 μprob ≤ θ*(coldMomentAt k:ℝ)) :
    lpNorm X 2 μprob ≤ θ*(coldInterpolationAt k:ℝ) := by
  have hkmem : k ∈ List.range 127 := List.mem_range.mpr (by omega)
  have hs := cold_graph_table_nonneg k hkmem
  have hM := cold_table_nonneg k (List.mem_range.mpr (by omega))
  have hp : (coldMeanAt k:ℝ)^9*(coldMomentAt k:ℝ)^10 ≤ (coldInterpolationAt k:ℝ)^19 := by
    exact_mod_cast (cold_interpolation_power_check k hkmem).2
  have hscale : (θ*(coldMeanAt k:ℝ))^9*(θ*(coldMomentAt k:ℝ))^10 ≤
      (θ*(coldInterpolationAt k:ℝ))^19 := by
    have hh := mul_le_mul_of_nonneg_left hp (pow_nonneg hθ 19)
    convert hh using 1 <;> ring
  exact (raw_l2_le_interpolated_caps μprob hX hn hmean hmoment).trans
    (interpolation_radical_le_of_power (mul_nonneg hθ (Rat.cast_nonneg.mpr hM.1))
      (mul_nonneg hθ (Rat.cast_nonneg.mpr hM.2))
      (mul_nonneg hθ (Rat.cast_nonneg.mpr hs.1)) hscale)

end ASDExplicitGamma.Cold
