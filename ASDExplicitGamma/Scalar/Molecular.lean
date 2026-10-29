module

public import ASDExplicitGamma.Variational.EnergyMap
public import Algsuperdiff.Section3.Annealed.RunningDiffusivity.Characterization
public import Algsuperdiff.Section3.Provider.Annealed.Monotonicity
public import Homogenization.Book.Ch02.Theorems.BasicVariationalIdentities
public import Homogenization.CoarseGraining.OriginCubeOpenBridge

/-! # Molecular lower bound for the genuine running diffusivity -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization Homogenization.Book
open Algsuperdiff.Section3
open MeasureTheory Filter

/-- The harmonic mean of a field with constant molecular symmetric part. -/
theorem averagedSymmPartInv_eq_inv_molecular {d : ℕ}
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (nu : ℝ)
    (hsymm : ∀ x, symmPart (a.toCoeffField x) = nu • (1 : Mat d)) :
    Ch02.averagedSymmPartInv U a = (nu • (1 : Mat d))⁻¹ := by
  ext i j
  change volumeAverage (U : Set (Vec d))
    (fun x => (symmPart (a.toCoeffField x))⁻¹ i j) = _
  simp_rw [hsymm]
  exact volumeAverage_const (Internal.Ch02.BookCh02.domain_volume_pos U).ne'

/-- The finite-volume upper-left block dominates the molecular matrix. -/
theorem molecularMatrix_le_coarseUpperLeft {d : ℕ} [NeZero d]
    (U : Ch02.Domain d) (a : Ch02.CoeffOn U) (nu : ℝ) (hnu : nu ≠ 0)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (hsymm : ∀ x, symmPart (a.toCoeffField x) = nu • (1 : Mat d)) :
    MatLoewnerLE (nu • (1 : Mat d))
      (Homogenization.coarseBlockMatrix (U : Set (Vec d)) a.toCoeffField).upperLeft := by
  rw [← Variational.energyMap_coarseBlockMatrix_eq U a hEll,
    Ch02.coarseBlockMatrix_upperLeft]
  have hh := Ch02.harmonicMean_le_sigmaStarCoarse U a
  have hinv : ((nu • (1 : Mat d))⁻¹)⁻¹ = nu • (1 : Mat d) := by
    rw [nonsing_inv_smul nu hnu (by simp), inv_one,
      nonsing_inv_smul nu⁻¹ (inv_ne_zero hnu) (by simp), inv_one, inv_inv]
  rw [averagedSymmPartInv_eq_inv_molecular U a nu hsymm, hinv] at hh
  exact hh.trans ((Ch02.sigmaStarCoarse_le_sigmaCoarse U a).trans
    (Ch02.sigmaCoarse_le_bCoarse U a))

/-- Pathwise molecular floor for a diagonal upper-left cutoff entry. -/
theorem nu_le_cutoff_coarseUpperLeft (M : ABKModel 2) (m n : ℤ)
    (omega : Cutoff.CutoffSample 2) (i : Fin 2) :
    M.nu ≤ (Homogenization.coarseBlockMatrix (cubeSet (originCube 2 n))
      (Cutoff.coefficientCutoff M.nu m omega).toFun).upperLeft i i := by
  rw [coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
  have h := molecularMatrix_le_coarseUpperLeft
    (Ch02.cubeDomain (originCube 2 n))
    (Cutoff.coefficientCutoffCoeffOn M m omega (originCube 2 n)) M.nu M.nu_pos.ne'
    (Cutoff.isEllipticFieldOn_coefficientCutoff_cube M m omega (originCube 2 n))
    (Cutoff.symmPart_coefficientCutoff M.nu m omega)
  have hi := h (Pi.single i 1)
  have hi' : (1 / 2 : ℝ) * M.nu ≤
      (1 / 2 : ℝ) * (Homogenization.coarseBlockMatrix
        (openCubeSet (originCube 2 n))
        (Cutoff.coefficientCutoff M.nu m omega).toFun).upperLeft i i := by
    simpa [vecDot, matVecMul, Pi.single_apply, Matrix.smul_apply] using hi
  linarith only [hi']

/-- The annealed finite-volume upper-left diagonal retains the molecular floor. -/
theorem nu_le_annealed_coarseUpperLeft (M : ABKModel 2) (m n : ℤ) (i : Fin 2) :
    M.nu ≤ (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M m) n).upperLeft i i := by
  have hInt := Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
    M m (originCube 2 n) (Sum.inl i) (Sum.inl i)
  change Integrable (fun a : RegCoeffField 2 =>
    (Homogenization.coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).upperLeft i i)
    (Cutoff.coefficientCutoffLaw M m) at hInt
  change M.nu ≤ ∫ a : RegCoeffField 2,
    (Homogenization.coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).upperLeft i i
    ∂(Cutoff.coefficientCutoffLaw M m)
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hInt ⊢
  rw [integral_map (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable
    hInt.aestronglyMeasurable]
  have hIntSample := (integrable_map_measure hInt.aestronglyMeasurable
    (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable).mp hInt
  calc
    M.nu = ∫ _omega : Cutoff.CutoffSample 2, M.nu ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
      simp only [integral_const, probReal_univ, one_smul]
    _ ≤ _ := integral_mono_ae (integrable_const _) hIntSample
      (Eventually.of_forall fun omega => nu_le_cutoff_coarseUpperLeft M m n omega i)

/-- SC-MOLECULAR-LOWER: the genuine running diffusivity is at least ν. -/
theorem nu_le_sigmaBar (M : ABKModel 2) (m : ℤ) :
    M.nu ≤ (Annealed.sigmaBar M m : ℝ) := by
  have hlim := (Annealed.sigmaBar_characterization M m).2.1
  have hentry := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim (Sum.inl (0 : Fin 2))))
    (Sum.inl (0 : Fin 2))
  have hentry' : Tendsto
      (fun n : ℕ => (Ch04.annealedBlockMatrixAtScale
        (Cutoff.coefficientCutoffLaw M m) (n : ℤ)).upperLeft 0 0)
      atTop (nhds (Annealed.sigmaBar M m : ℝ)) := by
    simpa [toFullBlockMat, Ch02.blockDiag] using hentry
  exact ge_of_tendsto hentry'
    (Eventually.of_forall fun n => nu_le_annealed_coarseUpperLeft M m (n : ℤ) 0)

end ASDExplicitGamma.Scalar
