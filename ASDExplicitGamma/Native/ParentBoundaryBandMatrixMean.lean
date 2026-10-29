module

public import ASDExplicitGamma.Native.ParentBoundaryBandMatrix

/-! Scalar expected diagonal blocks for the actual simultaneous weighted
band. Whole-sample symmetries retain every common-noise covariance. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open Response Scalar Triadic Variational Inverse
noncomputable section

/-- One of the two literal diagonal coarse blocks on the actual band. -/
def parentBoundaryBandDiagonalBlock (M : ABKModel 2) (n J : ℤ) (weights : ℤ → ℝ)
    (Q : TriadicCube 2) (plus : Bool) (omega : Cutoff.CutoffSample 2) : Mat 2 :=
  let A := coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M n J weights omega)
  if plus then A.upperLeft else A.lowerRight

/-- Measurability of every actual diagonal-block entry. -/
theorem parent_boundary_band_diagonal_entry_measurable (M : ABKModel 2) (n J : ℤ)
    (weights : ℤ → ℝ) (Q : TriadicCube 2) (plus : Bool) (i j : Fin 2) :
    Measurable (fun omega => parentBoundaryBandDiagonalBlock M n J weights Q plus omega i j) := by
  have hm := parent_boundary_band_full_coarse_measurable M n J weights Q
  cases plus
  · change Measurable (fun omega => toFullBlockMat
      (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M n J weights omega)) (Sum.inr i) (Sum.inr j))
    exact measurable_pi_iff.mp (measurable_pi_iff.mp hm _) _
  · change Measurable (fun omega => toFullBlockMat
      (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M n J weights omega)) (Sum.inl i) (Sum.inl j))
    exact measurable_pi_iff.mp (measurable_pi_iff.mp hm _) _

private theorem rotation_integral (M : ABKModel 2) (R : Mat 2) (hR : IsSignedPermutationMatrix R)
    (f : Cutoff.CutoffSample 2 → ℝ) (hf : Measurable f) :
    (∫ omega,f (Cutoff.rotateCutoffSample R hR omega) ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      ∫ omega,f omega ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi := integral_map (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (Cutoff.measurable_rotateCutoffSample R hR).aemeasurable hf.aestronglyMeasurable
  rw [Cutoff.map_rotateCutoffSample_cutoffSampleLaw M R hR] at hi
  exact hi.symm

private theorem diagonal_block_flip_off (M : ABKModel 2) (n J q : ℤ) (weights : ℤ → ℝ)
    (plus : Bool) (omega : Cutoff.CutoffSample 2) (i j : Fin 2) (hij : i≠j) :
    parentBoundaryBandDiagonalBlock M n J weights (originCube 2 q) plus
      (Cutoff.rotateCutoffSample (signFlipMatrix 0) (isSignedPermutationMatrix_signFlipMatrix 0) omega) i j=
      -parentBoundaryBandDiagonalBlock M n J weights (originCube 2 q) plus omega i j := by
  have hm := parent_boundary_band_coarse_sign_flip M n J q weights omega 0
  simp only [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube (originCube 2 q)] at hm
  have he := congrArg (fun A : BlockMat 2 => if plus then A.upperLeft i j else A.lowerRight i j) hm
  fin_cases i <;> fin_cases j <;> cases plus <;>
    simp_all [parentBoundaryBandDiagonalBlock,blockMatConj,signFlipMatrix,Matrix.mul_apply]

private theorem diagonal_block_swap (M : ABKModel 2) (n J q : ℤ) (weights : ℤ → ℝ)
    (plus : Bool) (omega : Cutoff.CutoffSample 2) :
    parentBoundaryBandDiagonalBlock M n J weights (originCube 2 q) plus
      (Cutoff.rotateCutoffSample (Matrix.swap ℝ 0 1) (isSignedPermutationMatrix_swap 0 1) omega) 0 0=
      parentBoundaryBandDiagonalBlock M n J weights (originCube 2 q) plus omega 1 1 := by
  have hm := parent_boundary_band_coarse_swap M n J q weights omega 0 1
  simp only [←coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube (originCube 2 q)] at hm
  have he := congrArg (fun A : BlockMat 2 => if plus then A.upperLeft 0 0 else A.lowerRight 0 0) hm
  cases plus <;> simpa [parentBoundaryBandDiagonalBlock,blockMatConj,Matrix.mul_apply,Matrix.swap] using he

/-- Each actual expected diagonal block is scalar on an origin square.
The assertion has no entry-integrability or symmetry premise: all needed
measurability and whole-sample laws are proved from the original model. -/
theorem parent_boundary_band_expected_diagonal_block (M : ABKModel 2) (n J q : ℤ)
    (weights : ℤ → ℝ) (plus : Bool) :
    ∃ c : ℝ,∀ i j : Fin 2,
      (∫ omega,parentBoundaryBandDiagonalBlock M n J weights (originCube 2 q) plus omega i j
        ∂(Cutoff.cutoffSampleLaw M).toMeasure)=if i=j then c else 0 := by
  let A := parentBoundaryBandDiagonalBlock M n J weights (originCube 2 q) plus
  have hm (i j : Fin 2) : Measurable (fun omega => A omega i j) :=
    parent_boundary_band_diagonal_entry_measurable M n J weights _ plus i j
  have hoff (i j : Fin 2) (hij : i≠j) :
      (∫ omega,A omega i j ∂(Cutoff.cutoffSampleLaw M).toMeasure)=0 := by
    have hi := rotation_integral M (signFlipMatrix 0) (isSignedPermutationMatrix_signFlipMatrix 0)
      (fun omega => A omega i j) (hm i j)
    have hpoint (omega : Cutoff.CutoffSample 2) :
        A (Cutoff.rotateCutoffSample (signFlipMatrix 0) (isSignedPermutationMatrix_signFlipMatrix 0) omega) i j=
          -A omega i j := diagonal_block_flip_off M n J q weights plus omega i j hij
    simp_rw [hpoint] at hi
    rw [integral_neg] at hi
    linarith only [hi]
  have hdiag : (∫ omega,A omega 0 0 ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      ∫ omega,A omega 1 1 ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    have hi := rotation_integral M (Matrix.swap ℝ 0 1) (isSignedPermutationMatrix_swap 0 1)
      (fun omega => A omega 0 0) (hm 0 0)
    simp_rw [show ∀ omega,A (Cutoff.rotateCutoffSample (Matrix.swap ℝ 0 1)
      (isSignedPermutationMatrix_swap 0 1) omega) 0 0=A omega 1 1 from
        diagonal_block_swap M n J q weights plus] at hi
    exact hi.symm
  refine ⟨∫ omega,A omega 0 0 ∂(Cutoff.cutoffSampleLaw M).toMeasure,?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · simp [A]
  · simpa using hoff 0 1 (by decide)
  · simpa using hoff 1 0 (by decide)
  · simpa using hdiag.symm


/-- The same scalar expected diagonal block on any translated source cell,
with exactly the same finite band and fixed original law. -/
theorem parent_boundary_band_expected_cell_block (M : ABKModel 2) (n J : ℤ)
    (weights : ℤ → ℝ) (Q : TriadicCube 2) (plus : Bool) :
    ∃ c : ℝ,∀ i j : Fin 2,
      (∫ omega,parentBoundaryBandDiagonalBlock M n J weights Q plus omega i j
        ∂(Cutoff.cutoffSampleLaw M).toMeasure)=if i=j then c else 0 := by
  obtain ⟨c,hc⟩ := parent_boundary_band_expected_diagonal_block M n J Q.scale weights plus
  refine ⟨c,?_⟩
  intro i j
  have he (omega : Cutoff.CutoffSample 2) : parentBoundaryBandDiagonalBlock M n J weights Q plus omega i j=
      parentBoundaryBandDiagonalBlock M n J weights (originCube 2 Q.scale) plus
        (Cutoff.translateCutoffSample (triadicCubeShift Q) omega) i j := by
    unfold parentBoundaryBandDiagonalBlock
    rw [parent_boundary_band_coarse_cell_translate]
  simp_rw [he]
  exact (integral_cutoffSample_vadd M (triadicCubeShift Q) (fun omega =>
    parentBoundaryBandDiagonalBlock M n J weights (originCube 2 Q.scale) plus omega i j)).trans (hc i j)

end
end ASDExplicitGamma.Native
