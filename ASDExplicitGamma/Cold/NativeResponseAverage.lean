module

public import ASDExplicitGamma.Cold.NativeResponseLaw
public import ASDExplicitGamma.Cold.SquareResponseOrder

/-! # The literal child average of the native true-frame full responses -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The actual finite child matrix average, with coefficient and true frame fixed at m. -/
def coldNativeResponseAverage (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) : FullBlockMat 2 :=
  fun i j => squareCellMean Q r (fun C => coldNativeResponse M m C.val ω i j)

/-- Normalization commutes literally with the actual child average. -/
theorem coldNativeResponseAverage_eq (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    coldNativeResponseAverage M m Q r ω = squareResponseAverage Q r (coldNativeCoefficient M m ω).toFun := by
  ext i j
  unfold coldNativeResponseAverage squareResponseAverage
  congr 1
  funext C
  rw [coldNativeResponse_eq_normalized]

/-- Actual native full responses satisfy the source matrix order on every partition. -/
theorem coldNativeResponseAverage_subadditive (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    (coldNativeResponseAverage M m Q r ω-coldNativeResponse M m Q ω).PosSemidef := by
  rw [coldNativeResponseAverage_eq,coldNativeResponse_eq_normalized]
  obtain ⟨Λ,hEll⟩ := coldNativeCoefficient_elliptic M m Q ω
  exact square_response_subadditive Q r
    (hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q))

/-- Expected entries of any actual translated cell equal those of its origin cell. -/
theorem coldNativeResponse_cell_mean (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponse M m Q) =
      matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponse M m (originCube 2 Q.scale)) := by
  ext i j
  exact ((coldNativeResponse_identDistrib M m Q).comp
    ((measurable_pi_apply j).comp (measurable_pi_apply i))).integral_eq

/-- Finite matrix averages retain their literal entrywise second moments. -/
theorem coldNativeResponseAverage_memLp (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (hA : ∀ C : SquareCells Q r, ∀ i j,
      MemLp (fun ω => coldNativeResponse M m C.val ω i j) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (i j : BlockCoord 2) :
    MemLp (fun ω => coldNativeResponseAverage M m Q r ω i j) 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
  (memLp_finsetSum Finset.univ (fun C _ => hA C i j)).const_mul _

/-- The full matrix child average has exactly the origin child matrix mean. -/
theorem coldNativeResponseAverage_mean (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (hA : ∀ C : SquareCells Q r, ∀ i j,
      Integrable (fun ω => coldNativeResponse M m C.val ω i j) (Cutoff.cutoffSampleLaw M).toMeasure) :
    matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponseAverage M m Q r) =
      matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponse M m (originCube 2 (Q.scale-r))) := by
  ext i j
  change (∫ ω, squareCellMean Q r (fun C => coldNativeResponse M m C.val ω i j)
    ∂(Cutoff.cutoffSampleLaw M).toMeasure) = _
  rw [integral_squareCellMean Q r (fun C => hA C i j)]
  have hh (C : SquareCells Q r) :
      (∫ ω, coldNativeResponse M m C.val ω i j ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        (matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponse M m (originCube 2 (Q.scale-r)))) i j := by
    have he := congrArg (fun A : FullBlockMat 2 => A i j) (coldNativeResponse_cell_mean M m C.val)
    rw [scale_eq_sub_of_mem_descendantsAtDepth C.property] at he
    exact he
  simp_rw [hh]
  exact squareCellMean_const Q r _

/-- Centering the average is the exact average of its centered cells. -/
theorem coldNativeResponseAverage_center (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ)
    (P : FullBlockMat 2) (ω : Cutoff.CutoffSample 2) :
    coldNativeResponseAverage M m Q r ω-P =
      (Fintype.card (SquareCells Q r):ℝ)⁻¹ • ∑ C : SquareCells Q r, (coldNativeResponse M m C.val ω-P) := by
  ext i j
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply]
  change squareCellMean Q r (fun C => coldNativeResponse M m C.val ω i j)-P i j =
    (Fintype.card (SquareCells Q r):ℝ)⁻¹ * (∑ C : SquareCells Q r, (coldNativeResponse M m C.val ω i j-P i j))
  simp only [squareCellMean,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_coe,nsmul_eq_mul,mul_sub]
  have hn : ((descendantsAtDepth Q r).card:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q r))
  field_simp

end ASDExplicitGamma.Cold
