module

public import ASDExplicitGamma.Cold.NativeResponseSpectral
public import ASDExplicitGamma.Cold.MatrixEntrySpectral
public import ASDExplicitGamma.Cold.BlockSymmetry
public import ASDExplicitGamma.Cold.ColdGraphBlocks
public import ASDExplicitGamma.Cold.MatrixMeanAlgebra

/-! # Full response laws and finite second moments at the true fixed frame -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
namespace ASDExplicitGamma.Cold

/-- Entrywise framing of an already doubled response. -/
def coldFullFrame (σ : ℝ) (A : FullBlockMat 2) : FullBlockMat 2 :=
  fun i j => match i,j with
    | Sum.inl _,Sum.inl _ => σ⁻¹*A i j
    | Sum.inr _,Sum.inr _ => σ*A i j
    | _,_ => A i j

theorem coldFullFrame_measurable (σ : ℝ) : Measurable (coldFullFrame σ) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  have hh (i j : BlockCoord 2) : Measurable (fun A : FullBlockMat 2 => A i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  cases i <;> cases j <;> first | exact (hh _ _).const_mul _ | exact hh _ _

theorem coldFullFrame_toFullBlockMat (σ : ℝ) (A : BlockMat 2) :
    coldFullFrame σ (toFullBlockMat A) = toFullBlockMat (Variational.frameMatrix σ A) := by
  ext i j
  cases i <;> cases j <;> rfl

/-- The entire actual response, including its cross blocks, has the origin-cell law. -/
theorem coldNativeResponse_identDistrib (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    ProbabilityTheory.IdentDistrib (coldNativeResponse M m Q)
      (coldNativeResponse M m (originCube 2 Q.scale))
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure := by
  let X := fun a : RegCoeffField 2 => toFullBlockMat (coarseBlockMatrix (cubeSet Q) a.toFun)
  let Y := fun a : RegCoeffField 2 => toFullBlockMat (coarseBlockMatrix (cubeSet (originCube 2 Q.scale)) a.toFun)
  have hX := (Cutoff.coefficientCutoffLaw_lawCarrier M m).aemeasurable_coarseFullBlockMatrix_cubeSet Q
  have hY := (Cutoff.coefficientCutoffLaw_lawCarrier M m).aemeasurable_coarseFullBlockMatrix_cubeSet (originCube 2 Q.scale)
  have he : ProbabilityTheory.IdentDistrib X Y (Cutoff.coefficientCutoffLaw M m) (Cutoff.coefficientCutoffLaw M m) :=
    ⟨hX,hY,Model.map_cutoffCoarseMatrix_cube_eq_origin M m Q⟩
  have hf := he.comp (coldFullFrame_measurable (Annealed.sigmaBar M m:ℝ))
  constructor
  · exact (coldNativeResponse_measurable M m Q).aemeasurable
  · exact (coldNativeResponse_measurable M m (originCube 2 Q.scale)).aemeasurable
  · have hh := hf.map_eq
    rw [Cutoff.coefficientCutoffLaw_eq_map] at hh
    rw [AEMeasurable.map_map_of_aemeasurable
      (by simpa only [← Cutoff.coefficientCutoffLaw_eq_map] using hf.aemeasurable_fst)
      (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable,
      AEMeasurable.map_map_of_aemeasurable
      (by simpa only [← Cutoff.coefficientCutoffLaw_eq_map] using hf.aemeasurable_snd)
      (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable] at hh
    unfold coldNativeResponse
    simpa only [Function.comp_def,X,Y,coldFullFrame_toFullBlockMat] using hh

/-- Actual entrywise sample means are the framed annealed matrix, without a moment premise. -/
theorem coldNativeResponse_mean (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponse M m Q) =
      toFullBlockMat (Variational.frameMatrix (Annealed.sigmaBar M m:ℝ)
        (Homogenization.Book.Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M m) (cubeSet Q))) := by
  ext i j
  have hi := Variational.integrable_frameMatrix_entry M m Q (Annealed.sigmaBar M m:ℝ) i j
  have he := Variational.integral_frameMatrix_entry M m (cubeSet Q) (Annealed.sigmaBar M m:ℝ) i j
  have ht (A : BlockMat 2) : toFullBlockMat A i j = blockMatEntry A i j := by cases i <;> cases j <;> rfl
  simp_rw [← ht] at hi he
  change (∫ ω, coldNativeResponse M m Q ω i j ∂(Cutoff.cutoffSampleLaw M).toMeasure) = _
  rw [← he]
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hi ⊢
  exact (integral_map (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable hi.aestronglyMeasurable).symm

/-- Both scalar mean blocks are nonnegative on the actual native sample space. -/
theorem coldNativeResponse_mean_blocks (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) :
    ∃ p q : ℝ, 0 ≤ p ∧ 0 ≤ q ∧
      matrixMean (Cutoff.cutoffSampleLaw M).toMeasure (coldNativeResponse M m Q) = 1+coldGraphBlockMean p q := by
  obtain ⟨p,q,hp,hq,he⟩ := exists_centered_mean_scalar_blocks M m Q.scale
  refine ⟨p,q,hp,hq,?_⟩
  rw [coldNativeResponse_mean]
  have hh := he (triadicCubeShift Q)
  rw [← cubeSet_eq_translateSet_originCube_of_triadicCube Q] at hh
  exact sub_eq_iff_eq_add.mp hh |>.trans (add_comm _ _)

/-- Every actual cell response has finite second moments as soon as its genuine trace does. -/
theorem coldNativeResponse_memLp_of_trace (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (hT : MemLp (coldNativeCellTrace M m Q) 2 (Cutoff.cutoffSampleLaw M).toMeasure) (i j : BlockCoord 2) :
    MemLp (fun ω => coldNativeResponse M m Q ω i j) 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
  memLp_matrix_entry_of_spectral _ _ hT (coldNativeResponse_measurable M m Q)
    (coldNativeCellTrace_nonneg M m Q) (coldNativeResponse_spectral M m Q) i j

/-- In particular all positive-lag response entries have finite second moments from root20. -/
theorem coldNativeResponse_memLp {M : ABKModel 2} {m : ℤ} {R : ℝ}
    (hroot : root20 M m ≤ ENNReal.ofReal R) (ell : ℕ) (i j : BlockCoord 2) :
    MemLp (fun ω => coldNativeResponse M m (originCube 2 (m+(ell:ℤ))) ω i j) 2
      (Cutoff.cutoffSampleLaw M).toMeasure :=
  coldNativeResponse_memLp_of_trace M m _
    ((coldNativeTrace_memLp hroot ell).mono_exponent (by norm_num)) i j

end ASDExplicitGamma.Cold
