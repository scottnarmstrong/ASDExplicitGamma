module

public import ASDExplicitGamma.Cold.ColdGraphBlocks
public import ASDExplicitGamma.Cold.MatrixFrobeniusMoment

/-! # The literal block-swap reflection on actual planar response matrices -/

@[expose] public section
noncomputable section
open Homogenization Matrix MeasureTheory
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Source block-swap conjugation. -/
def coldGraphReflection (A : FullBlockMat 2) : FullBlockMat 2 := coarseGramSwap*A*coarseGramSwap

/-- Conjugation swaps the two physical block coordinates in each entry. -/
theorem coldGraphReflection_apply (A : FullBlockMat 2) (i j : BlockCoord 2) :
    coldGraphReflection A i j = A i.swap j.swap := by
  cases i <;> cases j <;>
    simp [coldGraphReflection,Matrix.mul_apply,coarseGramSwap,toFullBlockMat,Book.Ch02.blockR,
      Fintype.sum_sum_type,Matrix.one_apply]

/-- The reflection preserves the actual Frobenius square, including nonsymmetric matrices. -/
theorem coldGraphReflection_frobenius (A : FullBlockMat 2) :
    matrixFrobeniusSq (coldGraphReflection A) = matrixFrobeniusSq A := by
  unfold matrixFrobeniusSq
  simp_rw [coldGraphReflection_apply]
  simp only [Fintype.sum_sum_type,Sum.swap_inl,Sum.swap_inr,Finset.sum_add_distrib]
  ring

/-- The same entry permutation preserves the actual annealed matrix norm. -/
theorem coldGraphReflection_L2 {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω) (A : Ω → FullBlockMat 2) :
    matrixFrobeniusL2 ℙ (fun ω => coldGraphReflection (A ω)) = matrixFrobeniusL2 ℙ A := by
  unfold matrixFrobeniusL2
  simp_rw [coldGraphReflection_frobenius]

/-- The source unequal expected blocks are interchanged, not equated. -/
theorem coldGraphReflection_blockMean (p q : ℝ) :
    coldGraphReflection (coldGraphBlockMean p q) = coldGraphBlockMean q p := by
  ext i j
  rw [coldGraphReflection_apply]
  cases i <;> cases j <;>
    simp [coldGraphBlockMean,toFullBlockMat,Book.Ch02.blockDiag]

/-- Actual reflection preserves entrywise L2 membership. -/
theorem memLp_coldGraphReflection {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {A : Ω → FullBlockMat 2} (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ) (i j : BlockCoord 2) :
    MemLp (fun ω => coldGraphReflection (A ω) i j) 2 ℙ := by
  simpa only [coldGraphReflection_apply] using hA i.swap j.swap

/-- Reflection commutes with the ordinary matrix expectation. -/
theorem matrixMean_coldGraphReflection {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω)
    (A : Ω → FullBlockMat 2) :
    matrixMean ℙ (fun ω => coldGraphReflection (A ω)) = coldGraphReflection (matrixMean ℙ A) := by
  ext i j
  simp only [matrixMean,coldGraphReflection_apply]

end ASDExplicitGamma.Cold
