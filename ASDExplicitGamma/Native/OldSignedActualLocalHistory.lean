module

public import ASDExplicitGamma.Native.OldSignedBankDirectionalRare
public import ASDExplicitGamma.Native.OldSignedPartialFrameHistory
public import ASDExplicitGamma.Native.OldSignedHistoryMoments

/-! The actual common inverse-history multiplier for every AN source cell. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The common local inverse history is measurable in the actual insertion law. -/
theorem old_signed_local_history_measurable (M : ABKModel 2) (n : ℤ) (t : ℝ) :
    Measurable (rawShellBandLocalHistory M n 1 t) :=
  raw_shell_weighted_local_history_measurable M n (n+(1:ℕ)) (bankPartialInsertionWeights n 1 t)

/-- Every actual AN cell uses the same bank split. Finiteness is supplied by
the bank before converting the extended history to a real number. -/
theorem old_signed_actual_cell_inverse_history_split
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r≤5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      oldSignedInverseHistory U (oldSignedPartialFrameField M n 1 t ω)≤
        rawShellBandLocalHistory M n 1 t ω ∧
      rawShellBandLocalHistory M n 1 t ω≤(3683/2500:ℝ)+oldSignedLocalBankRemainder M n t ω := by
  have hb := raw_shell_band_local_inverse_bank M h hM hg n 1 (by norm_num) t ht hpast
  filter_upwards [hb.history_finite,hb.history_le] with ω hfinite hle
  refine ⟨raw_shell_band_source_mesh_history_le M n 1 (by norm_num) t ht ω r hr
    hfinite.ne hU,?_⟩
  have hh := ENNReal.toReal_mono (by simp) hle
  rw [ENNReal.toReal_add (by simp) (by simp),ENNReal.toReal_ofReal (by norm_num [inverseBankCap]),
    ENNReal.toReal_ofReal (hb.remainder_nonneg ω)] at hh
  simpa only [rawShellBandLocalHistory,oldSignedLocalBankRemainder,inverseBankCap,
    Rat.cast_div,Rat.cast_ofNat] using hh

/-- The actual common inverse multiplier has the exact order-two bank cap. -/
theorem old_signed_actual_local_history_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    MemLp (rawShellBandLocalHistory M n 1 t) 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm (rawShellBandLocalHistory M n 1 t) 2 (Cutoff.cutoffSampleLaw M).toMeasure≤(3683/2500:ℝ) := by
  have h128 := raw_shell_band_local_history_L128 M h hM hg n 1 (by norm_num) t ht hpast
  have h2 := (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2:ℝ≥0∞)≤128)).trans h128
  refine ⟨lt_of_le_of_lt h2 ENNReal.ofReal_lt_top,?_⟩
  change (eLpNorm (rawShellBandLocalHistory M n 1 t) 2 (Cutoff.cutoffSampleLaw M).toMeasure).toReal≤_
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h2).trans_eq
    (ENNReal.toReal_ofReal (by norm_num))

end
end ASDExplicitGamma.Native
