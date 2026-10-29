module

public import ASDExplicitGamma.Scalar.LawCoarseShift
public import ASDExplicitGamma.Scalar.Molecular
public import Algsuperdiff.Section3.Provider.BadEvents.LiteralMeasurabilityEngine

/-! Exact finite-volume annealed top-block covariance under the source scale shift. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Variational Book MeasureTheory
open Algsuperdiff.Section3

/-- The genuine annealed upper-left entry is its literal cutoff-sample expectation. -/
theorem annealed_top_entry_cutoff_samples (M : ABKModel 2) (n k : ℤ) (i j : Fin 2) :
    (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M n) k).upperLeft i j=
      ∫ ω,(coarseBlockMatrix (cubeSet (originCube 2 k))
        (Cutoff.coefficientCutoff M.nu n ω).toFun).upperLeft i j ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi := Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
    M n (originCube 2 k) (Sum.inl i) (Sum.inl j)
  change Integrable (fun a : RegCoeffField 2 =>
    (coarseBlockMatrix (cubeSet (originCube 2 k)) a.toFun).upperLeft i j)
    (Cutoff.coefficientCutoffLaw M n) at hi
  change (∫ a : RegCoeffField 2,(coarseBlockMatrix (cubeSet (originCube 2 k)) a.toFun).upperLeft i j
    ∂Cutoff.coefficientCutoffLaw M n)=_
  rw [Cutoff.coefficientCutoffLaw_eq_map] at hi ⊢
  exact integral_map (Cutoff.measurable_coefficientCutoff M.nu n).aemeasurable hi.aestronglyMeasurable

/-- Every actual top-block entry is measurable on the honest cutoff-sample carrier. -/
theorem measurable_cutoff_top_entry (M : ABKModel 2) (n k : ℤ) (i j : Fin 2) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      (coarseBlockMatrix (cubeSet (originCube 2 k))
        (Cutoff.coefficientCutoff M.nu n ω).toFun).upperLeft i j) := by
  have hm := Provider.BadEvents.measurable_comp_coarseB_cubeSet (Cutoff.measurable_coefficientCutoff M.nu n)
    (fun ω => Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M n ω) (originCube 2 k)
  exact (measurable_pi_iff.mp (measurable_pi_iff.mp hm i)) j

/-- Integer shell scale shifts transport the actual finite-volume annealed top block. -/
theorem annealed_top_entry_scale_shift (M : ABKModel 2) (j k : ℕ) (n : ℤ) (i l : Fin 2) :
    (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw M (n+(j:ℤ))) ((j+k:ℕ):ℤ)).upperLeft i l=
      Real.rpow 3 (M.gamma*(j:ℝ))*
        (Ch04.annealedBlockMatrixAtScale (Cutoff.coefficientCutoffLaw (viscosityShiftModel M (j:ℤ)) n)
          (k:ℤ)).upperLeft i l := by
  rw [annealed_top_entry_cutoff_samples,annealed_top_entry_cutoff_samples]
  have hf := measurable_cutoff_top_entry (viscosityShiftModel M (j:ℤ)) n (k:ℤ) i l
  let f : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    (coarseBlockMatrix (cubeSet (originCube 2 (k:ℤ)))
      (Cutoff.coefficientCutoff (viscosityShiftModel M (j:ℤ)).nu n ω).toFun).upperLeft i l
  have hm : (Cutoff.cutoffSampleLaw (viscosityShiftModel M (j:ℤ))).toMeasure=
      (Cutoff.cutoffSampleLaw M).toMeasure := rfl
  rw [hm]
  have he : (∫ ω,f (cutoffScaleShift M.gamma (j:ℤ) ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure)=
      ∫ ω,f ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    have hf' : AEStronglyMeasurable f
        (Measure.map (cutoffScaleShift M.gamma (j:ℤ)) (Cutoff.cutoffSampleLaw M).toMeasure) := by
      rw [cutoff_scale_shift_preserves_law]
      exact hf.aestronglyMeasurable
    have hi := integral_map (measurable_cutoff_scale_shift M.gamma (j:ℤ)).aemeasurable hf'
    rw [cutoff_scale_shift_preserves_law] at hi
    exact hi.symm
  calc
    _ = ∫ ω,Real.rpow 3 (M.gamma*(j:ℝ))*f (cutoffScaleShift M.gamma (j:ℤ) ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        change (coarseBlockMatrix (cubeSet (originCube 2 ((j+k:ℕ):ℤ)))
          (Cutoff.coefficientCutoff M.nu (n+(j:ℤ)) ω).toFun).upperLeft i l=_
        rw [cutoff_coarse_scale_shift]
        have hsq : (Real.sqrt (Real.rpow 3 (M.gamma*(j:ℝ))))^2=Real.rpow 3 (M.gamma*(j:ℝ)) := by
          convert Real.sq_sqrt (show 0 ≤ Real.rpow 3 (M.gamma*(j:ℝ)) from
            Real.rpow_nonneg (by norm_num) _) using 1
        simp only [coarseMatrixRescale,Matrix.smul_apply,smul_eq_mul,hsq]
        rfl
    _ = _ := by rw [integral_const_mul,he]

end ASDExplicitGamma.Scalar
