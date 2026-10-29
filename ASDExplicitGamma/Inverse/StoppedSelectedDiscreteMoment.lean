module

public import ASDExplicitGamma.Inverse.StoppedSelectedMaximum
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Exact atomic moment formula for a selected natural-valued height. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The complete tail selector contains exactly one atom on each tail sample. -/
theorem discrete_height_tail_sum {Ω : Type*} (H : Ω → ℕ) (Hs : ℕ)
    (c : ℕ → ℝ≥0∞) (ω : Ω) :
    (if Hs < H ω then c (H ω-(Hs+1)) else 0) =
      ∑' n : ℕ, if H ω=Hs+1+n then c n else 0 := by
  classical
  by_cases hω : Hs < H ω
  · simp only [hω,ite_true]
    have hn : H ω=Hs+1+(H ω-(Hs+1)) := by omega
    symm
    rw [tsum_eq_single (H ω-(Hs+1))]
    · exact ite_eq_left hn
    · intro n hne
      have hn' : ¬H ω=Hs+1+n := by omega
      exact ite_eq_right hn'
  · simp only [hω,ite_false]
    symm
    have he : (fun n : ℕ => if H ω=Hs+1+n then c n else 0) = fun _ => 0 := by
      funext n
      exact ite_eq_right (by omega)
    rw [he,tsum_zero]

/-- The complete selected-height tail moment equals the full sum of its
atomic probabilities. No relation to a wave or density is assumed. -/
theorem discrete_height_tail_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (H : Ω → ℕ) (hH : Measurable H) (Hs : ℕ)
    (c : ℕ → ℝ≥0∞) (p : ℝ) (hp : 0 < p) :
    (∫⁻ ω, (if Hs < H ω then c (H ω-(Hs+1)) else 0)^p ∂μ) =
      ∑' n : ℕ, (c n)^p*μ {ω | H ω=Hs+1+n} := by
  have he (ω : Ω) : (if Hs < H ω then c (H ω-(Hs+1)) else 0)^p =
      ∑' n : ℕ, ({ω | H ω=Hs+1+n} : Set Ω).indicator (fun _ => (c n)^p) ω := by
    have hh := discrete_height_tail_sum H Hs (fun n => (c n)^p) ω
    convert hh using 1
    · by_cases hω : Hs < H ω <;> simp only [hω,ite_true,ite_false,ENNReal.zero_rpow_of_pos hp]
    · apply tsum_congr
      intro n
      simp only [Set.indicator,Set.mem_ofPred_eq]
  simp_rw [he]
  have hE (n : ℕ) : MeasurableSet {ω | H ω=Hs+1+n} :=
    hH (measurableSet_singleton _)
  rw [lintegral_tsum (fun n =>
    (measurable_const.indicator (hE n)).aemeasurable)]
  apply tsum_congr
  intro n
  rw [lintegral_indicator (hE n),lintegral_const]
  simp only [Measure.restrict_apply_univ]

end
end ASDExplicitGamma.Inverse
