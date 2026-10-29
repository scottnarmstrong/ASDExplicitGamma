module

public import ASDExplicitGamma.Native.OldSignedActualLocalHistory

/-! Sharp first and reciprocal-offset moments of the common local bank. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
noncomputable section

/-- The actual inverse multiplier and its reciprocal offset retain the bank
constant under the first and second moments used by the flat error bill. -/
theorem old_signed_actual_local_history_moments
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    let B := rawShellBandLocalHistory M n 1 t
    Integrable B (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,B ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤(3683/2500:ℝ) ∧
    Integrable (fun ω => (B ω+1)^2) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,(B ω+1)^2 ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤((3683/2500:ℝ)+1)^2 := by
  intro B
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hb := old_signed_actual_local_history_L2 M h hM hg n hpast t ht
  have hb0 (ω) : 0≤B ω := ENNReal.toReal_nonneg
  have hfirst := old_signed_history_first_second_moments μ B (3683/2500) hb.1 hb0 (by norm_num) hb.2
  have hoff : MemLp (fun ω => B ω+1) 2 μ := hb.1.add (memLp_const (1:ℝ))
  have hone : lpNorm (fun _ : Cutoff.CutoffSample 2 => (1:ℝ)) 2 μ=1 := by
    rw [lpNorm_const' (by norm_num) (by norm_num)]
    simp only [norm_one,probReal_univ,Real.one_rpow,mul_one]
  have hnorm : lpNorm (fun ω => B ω+1) 2 μ≤(3683/2500:ℝ)+1 := by
    have hh := lpNorm_add_le (g := fun _ => (1:ℝ)) hb.1 (by norm_num)
    rw [hone] at hh
    exact hh.trans (add_le_add hb.2 le_rfl)
  have hsecond := (old_signed_history_first_second_moments μ (fun ω => B ω+1)
    ((3683/2500:ℝ)+1) hoff (fun ω => add_nonneg (hb0 ω) (by norm_num)) (by norm_num) hnorm).2
  exact ⟨hb.1.integrable (by norm_num),hfirst.1,
    (memLp_two_iff_integrable_sq hoff.aestronglyMeasurable).mp hoff,hsecond⟩

end
end ASDExplicitGamma.Native
