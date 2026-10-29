module

public import ASDExplicitGamma.Cold.NativeGraphFourColor

/-! # Actual trace variance of the native full-response child average -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The full child trace excess is exactly the average of the genuine child trace defects. -/
theorem coldNativeResponseAverage_trace (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    (coldNativeResponseAverage M m Q r ω).trace-4 =
      squareCellMean Q r (fun C => coldNativeCellTrace M m C.val ω) := by
  have he := squareCellMean_sum Q r Finset.univ
    (fun i C => coldNativeResponse M m C.val ω i i)
  change (∑ i, squareCellMean Q r (fun C => coldNativeResponse M m C.val ω i i))-4 = _
  rw [← he,← squareCellMean_const Q r 4,← squareCellMean_sub]
  congr 1
  funext C
  exact coldNativeResponse_trace M m C.val ω

/-- The actual centered child trace average has the sharp four-colour L2 decay. -/
theorem cold_native_trace_average_center (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (Q : TriadicCube 2) (r : ℕ) (hm : m ≤ Q.scale-(r:ℤ)) {L : ℝ}
    (hT : ∀ C : SquareCells Q r, MemLp (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hL : ∀ C : SquareCells Q r, lpNorm (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L) :
    lpNorm (fun ω => (coldNativeResponseAverage M m Q r ω).trace-4-
      ∫ a, cutoffTraceDefect M m (Q.scale-r) a ∂(Cutoff.cutoffSampleLaw M).toMeasure) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ 2*(3:ℝ)^(-(r:ℝ))*L := by
  let μprob := (Cutoff.cutoffSampleLaw M).toMeasure
  let μ := ∫ a, cutoffTraceDefect M m (Q.scale-r) a ∂μprob
  let Y := fun (C : SquareCells Q r) (ω : Cutoff.CutoffSample 2) => coldNativeCellTrace M m C.val ω-μ
  have hmean (C : SquareCells Q r) : (∫ ω, coldNativeCellTrace M m C.val ω ∂μprob) = μ := by
    rw [coldNativeCellTrace_integral,scale_eq_sub_of_mem_descendantsAtDepth C.property]
  have hY (C : SquareCells Q r) : MemLp (Y C) 2 μprob := (hT C).sub (memLp_const μ)
  have hInd : ∀ c : Fin 4, ProbabilityTheory.iIndepFun
      (fun C : {C : SquareCells Q r // coldCubeColor C.val = c} => Y C.val) μprob :=
    cold_native_four_color_independent (X := Y) M h hM m (Q.scale-r) hm (fun C : SquareCells Q r => C.val)
      Subtype.val_injective (fun C => scale_eq_sub_of_mem_descendantsAtDepth C.property)
      (fun C => (coldNativeCellTrace_local M m C.val).sub_const μ)
  have hzero (C : SquareCells Q r) : (∫ ω, Y C ω ∂μprob) = 0 := by
    change (∫ ω, coldNativeCellTrace M m C.val ω-μ ∂μprob) = 0
    rw [integral_sub ((hT C).integrable (by norm_num)) (integrable_const _),integral_const,
      probReal_univ,one_smul,hmean,sub_self]
  have hcap (C : SquareCells Q r) : lpNorm (Y C) 2 μprob ≤ L := by
    have hh := lpNorm_sub_mean_le μprob (by norm_num : (2:ℝ) ≤ 2)
      (show MemLp (coldNativeCellTrace M m C.val) (ENNReal.ofReal 2) μprob by simpa using hT C)
      (Filter.Eventually.of_forall (coldNativeCellTrace_nonneg M m C.val))
    rw [hmean C] at hh
    have hh' : lpNorm (Y C) 2 μprob ≤ lpNorm (coldNativeCellTrace M m C.val) 2 μprob := by
      simpa only [ENNReal.ofReal_ofNat] using hh
    exact hh'.trans (hL C)
  have hi : Nonempty (SquareCells Q r) := inferInstance
  obtain ⟨C0⟩ := hi
  have hLn : 0 ≤ L := lpNorm_nonneg.trans (hL C0)
  have hh := four_color_two_centered_average (fun C : SquareCells Q r => coldCubeColor C.val)
    (Y := Y) hY hInd hzero hLn hcap
  rw [cold_matrix_color_decay] at hh
  have he : (fun ω => (coldNativeResponseAverage M m Q r ω).trace-4-μ) =
      (fun ω => (∑ C, Y C ω)/(Fintype.card (SquareCells Q r):ℝ)) := by
    funext ω
    rw [coldNativeResponseAverage_trace,← squareCellMean_const Q r μ,← squareCellMean_sub]
    change squareCellMean Q r (fun C => Y C ω) = _
    unfold squareCellMean
    rw [Fintype.card_coe]
    ring
  rw [he]
  exact hh

end ASDExplicitGamma.Cold
