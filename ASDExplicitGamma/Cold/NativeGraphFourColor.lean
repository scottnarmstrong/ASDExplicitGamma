module

public import ASDExplicitGamma.Cold.NativeResponseAverage
public import ASDExplicitGamma.Cold.NativeResponseMoment
public import ASDExplicitGamma.Cold.FourColorMatrix
public import ASDExplicitGamma.Cold.FourColorTwo
public import ASDExplicitGamma.Cold.NativeCellIndex

/-! # Actual four-colour matrix fluctuations for native graph candidates -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The exact spatial population gives the source 3^{-r} decay. -/
theorem cold_matrix_color_decay (Q : TriadicCube 2) (r : ℕ) :
    2/Real.sqrt (Fintype.card (SquareCells Q r):ℝ) = 2*(3:ℝ)^(-(r:ℝ)) := by
  rw [cold_square_cells_card,Nat.cast_pow]
  norm_num only [Nat.cast_ofNat]
  have he : (9:ℝ)^r = ((3:ℝ)^r)^2 := by rw [← pow_mul]; norm_num [pow_mul']
  rw [he,Real.sqrt_sq (pow_nonneg (by norm_num) r),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3),Real.rpow_natCast]
  rfl

/-- The actual independent child matrices give the sharp dimension-free centered matrix cap. -/
theorem cold_native_response_average_center (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (Q : TriadicCube 2) (r : ℕ) (hm : m ≤ Q.scale-(r:ℤ)) {D L : ℝ}
    (hT : ∀ C : SquareCells Q r, MemLp (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hD : ∀ C : SquareCells Q r, (∫ ω, coldNativeCellTrace M m C.val ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ D)
    (hL : ∀ C : SquareCells Q r, lpNorm (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L) :
    matrixFrobeniusL2 (Cutoff.cutoffSampleLaw M).toMeasure (fun ω => coldNativeResponseAverage M m Q r ω-
      matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponseAverage M m Q r)) ≤
      2*(3:ℝ)^(-(r:ℝ))*Real.sqrt (2*D+L^2) := by
  let μprob := (Cutoff.cutoffSampleLaw M).toMeasure
  let P := matrixMean μprob (coldNativeResponse M m (originCube 2 (Q.scale-r)))
  let Y := fun (C : SquareCells Q r) (ω : Cutoff.CutoffSample 2) => coldNativeResponse M m C.val ω-P
  have hA (C : SquareCells Q r) := coldNativeResponse_memLp_of_trace M m C.val (hT C)
  have hYP (C : SquareCells Q r) : matrixMean μprob (coldNativeResponse M m C.val) = P := by
    rw [coldNativeResponse_cell_mean,scale_eq_sub_of_mem_descendantsAtDepth C.property]
  have hYPX : matrixMean μprob (coldNativeResponseAverage M m Q r) = P :=
    coldNativeResponseAverage_mean M m Q r (fun C i j => (hA C i j).integrable (by norm_num))
  have hY (C : SquareCells Q r) (i j : BlockCoord 2) : MemLp (fun ω => Y C ω i j) 2 μprob :=
    (hA C i j).sub (memLp_const (P i j))
  have hsubmeas : Measurable (fun A : FullBlockMat 2 => A-P) := by
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    change Measurable (fun A : FullBlockMat 2 => A i j-P i j)
    have hh : Measurable (fun A : FullBlockMat 2 => A i j) :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    exact hh.sub_const (P i j)
  have hInd : ∀ c : Fin 4, ProbabilityTheory.iIndepFun
      (fun C : {C : SquareCells Q r // coldCubeColor C.val = c} => Y C.val) μprob := by
    exact cold_native_four_color_independent (X := Y) M h hM m (Q.scale-r) hm (fun C : SquareCells Q r => C.val)
      Subtype.val_injective (fun C => scale_eq_sub_of_mem_descendantsAtDepth C.property)
      (fun C => hsubmeas.comp (coldNativeResponse_local M m C.val))
  have hzero (C : SquareCells Q r) (i j : BlockCoord 2) : (∫ ω, Y C ω i j ∂μprob) = 0 := by
    change (∫ ω, coldNativeResponse M m C.val ω i j-P i j ∂μprob) = 0
    rw [integral_sub ((hA C i j).integrable (by norm_num)) (integrable_const _),integral_const,probReal_univ,one_smul]
    exact sub_eq_zero.mpr (congrArg (fun A : FullBlockMat 2 => A i j) (hYP C))
  have hcap (C : SquareCells Q r) : matrixFrobeniusL2 μprob (Y C) ≤ Real.sqrt (2*D+L^2) := by
    have hh := coldNativeResponse_center_cap M m C.val (hT C) (hD C) (hL C)
    rw [hYP C] at hh
    exact hh
  have hh := four_color_matrix_centered_average (fun C : SquareCells Q r => coldCubeColor C.val)
    (Y := Y) hY hInd hzero (Real.sqrt_nonneg _) hcap
  rw [cold_matrix_color_decay] at hh
  have he : (fun ω => coldNativeResponseAverage M m Q r ω-matrixMean μprob (coldNativeResponseAverage M m Q r)) =
      (fun ω => (Fintype.card (SquareCells Q r):ℝ)⁻¹ • ∑ C, Y C ω) := by
    funext ω
    rw [hYPX]
    exact coldNativeResponseAverage_center M m Q r P ω
  rw [he]
  exact hh

end ASDExplicitGamma.Cold
