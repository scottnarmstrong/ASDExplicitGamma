module

public import ASDExplicitGamma.Inverse.HistoryTraceMonotone

/-! One-cell trace moments decrease with the physical observation scale. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Inverse
open Algsuperdiff.Section3
open scoped ENNReal

/-- Subadditivity and stationarity bound the actual parent trace norm by the smaller cell norm. -/
theorem trace_cell_L20_le_descendant_scale (M : ABKModel 2) (n : ℤ) (Q : TriadicCube 2) (j : ℕ) :
    eLpNorm (cutoffTraceDefect M n Q.scale) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      eLpNorm (cutoffTraceDefect M n (Q.scale-(j:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
  classical
  let s := descendantsAtDepth Q j
  let f (R : TriadicCube 2) (ω : Cutoff.CutoffSample 2) := ENNReal.ofReal (historyTrace M n R ω)
  let c : ℝ≥0∞ := ENNReal.ofReal ((s.card:ℝ)⁻¹)
  have hcard : 0 < s.card := Finset.card_pos.mpr (descendantsAtDepth_nonempty Q j)
  have hpoint (ω : Cutoff.CutoffSample 2) :
      f Q ω ≤ c*∑ R ∈ s,f R ω := by
    have h := ENNReal.ofReal_le_ofReal (history_trace_subadditive M n Q j ω)
    unfold descendantsAverage at h
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg _)),
      ENNReal.ofReal_sum_of_nonneg (fun R _ => history_trace_nonneg M n R ω)] at h
    exact h
  have hnorm (R : TriadicCube 2) (hR : R ∈ s) :
      eLpNorm (f R) 20 (Cutoff.cutoffSampleLaw M).toMeasure=
        eLpNorm (cutoffTraceDefect M n (Q.scale-(j:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [history_trace_ofReal_norm]
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR]
  have hs : Measurable (fun ω => ∑ R ∈ s,f R ω) :=
    Finset.measurable_sum _ (fun R _ => (history_trace_measurable M n R).ennreal_ofReal)
  have hm := eLpNorm_mono_enorm_ae (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (g := fun ω => c*∑ R ∈ s,f R ω) ((history_trace_measurable M n Q).ennreal_ofReal).aestronglyMeasurable
    (p:=20) (Filter.Eventually.of_forall fun ω => by simpa only [enorm_eq_self] using hpoint ω)
  rw [history_trace_ofReal_norm,history_constant_mul_L20 _ c _ hs] at hm
  have he : (∑ R ∈ s,f R)=(fun ω => ∑ R ∈ s,f R ω) := by
    funext ω
    simp only [Finset.sum_apply]
  have hsum := eLpNorm_sum_le (μ:=(Cutoff.cutoffSampleLaw M).toMeasure) (f:=f) (s:=s)
    (by norm_num : (1:ℝ≥0∞) ≤ 20)
  rw [he] at hsum
  have hb := hm.trans (mul_le_mul_of_nonneg_left hsum (zero_le : (0:ℝ≥0∞) ≤ c))
  have heq : (∑ R ∈ s,eLpNorm (f R) 20 (Cutoff.cutoffSampleLaw M).toMeasure)=
      (s.card:ℝ≥0∞)*eLpNorm (cutoffTraceDefect M n (Q.scale-(j:ℤ))) 20 (Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [Finset.sum_congr rfl hnorm]
    simp only [Finset.sum_const,nsmul_eq_mul]
  rw [heq,← mul_assoc] at hb
  have hc : c*(s.card:ℝ≥0∞)=1 := by
    dsimp only [c]
    rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hcard),ENNReal.ofReal_natCast,
      ENNReal.inv_mul_cancel (by exact_mod_cast hcard.ne') (by simp)]
  simpa only [hc,one_mul] using hb

/-- The actual one-cell L20 trace moments are antitone in the integer observation label. -/
theorem trace_cell_L20_antitone (M : ABKModel 2) (n : ℤ) :
    Antitone (fun k : ℤ => eLpNorm (cutoffTraceDefect M n k) 20 (Cutoff.cutoffSampleLaw M).toMeasure) := by
  intro a b hab
  let j := (b-a).toNat
  have hj : (j:ℤ)=b-a := Int.toNat_of_nonneg (by omega)
  have h := trace_cell_L20_le_descendant_scale M n (originCube 2 b) j
  simpa only [originCube,show b-(j:ℤ)=a by omega] using h

end ASDExplicitGamma.Scalar
