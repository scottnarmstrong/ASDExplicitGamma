module

public import ASDExplicitGamma.Cold.NativeGraphTraceMoment

/-! # Raw second moments descend through actual trace subadditivity -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- A literal finite average preserves a raw L2 cap. -/
theorem cold_trace_average_two_lpNorm_le {Ω ι : Type*} [MeasurableSpace Ω] {μprob : Measure Ω}
    [Fintype ι] [Nonempty ι] {X : ι → Ω → ℝ} {L : ℝ}
    (hX : ∀ i, MemLp (X i) 2 μprob) (hcap : ∀ i, lpNorm (X i) 2 μprob ≤ L) :
    lpNorm (fun ω => (∑ i, X i ω)/(Fintype.card ι:ℝ)) 2 μprob ≤ L := by
  classical
  rw [lpNorm_fun_div_natCast Fintype.card_ne_zero]
  have hh := (lpNorm_sum_le (s := Finset.univ) (fun i _ => hX i) (by norm_num : (1:ℝ≥0∞) ≤ 2)).trans
    (Finset.sum_le_sum (fun i _ => hcap i))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  have he : (fun ω => ∑ i, X i ω) = ∑ i, X i := by funext ω; simp only [Finset.sum_apply]
  rw [he]
  apply (div_le_iff₀ (Nat.cast_pos.mpr Fintype.card_pos)).mpr
  simpa only [mul_comm] using hh

/-- Actual pathwise subadditivity preserves the raw child L2 cap at the parent. -/
theorem coldNativeCellTrace_two_le_children (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ) {L : ℝ}
    (hT : ∀ C : SquareCells Q r, MemLp (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hL : ∀ C : SquareCells Q r, lpNorm (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L) :
    lpNorm (coldNativeCellTrace M m Q) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L := by
  let X := fun (C : SquareCells Q r) => coldNativeCellTrace M m C.val
  let A := fun ω => (∑ C, X C ω)/(Fintype.card (SquareCells Q r):ℝ)
  have hA : MemLp A 2 (Cutoff.cutoffSampleLaw M).toMeasure := by
    simpa only [A,X,div_eq_mul_inv,mul_comm] using
      (memLp_finsetSum Finset.univ (fun C _ => hT C)).const_mul (Fintype.card (SquareCells Q r):ℝ)⁻¹
  have he (ω : Cutoff.CutoffSample 2) : squareCellMean Q r (fun C => X C ω) = A ω := by
    unfold squareCellMean A
    rw [Fintype.card_coe]
    ring
  have hh : lpNorm (coldNativeCellTrace M m Q) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      lpNorm A 2 (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply cold_lpNorm_mono_ae hA
    apply Filter.Eventually.of_forall
    intro ω
    have hsub := coldNativeCellTrace_subadditive M m Q r ω
    rw [he] at hsub
    have hn := coldNativeCellTrace_nonneg M m Q ω
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hn,abs_of_nonneg (hn.trans hsub)]
    exact hsub
  exact hh.trans (cold_trace_average_two_lpNorm_le hT hL)

end ASDExplicitGamma.Cold
