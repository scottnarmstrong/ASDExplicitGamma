module

public import ASDExplicitGamma.Main.HeatIdentity
public import ASDExplicitGamma.Variational.TrueFrame

/-! The initial inverse-trace value in the actual OLD frame. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization Homogenization.Book MeasureTheory ProbabilityTheory
open Algsuperdiff.Section3 ASDExplicitGamma.Gaussian

/-- The actual inserted inverse trace starts at least at two.  At zero insertion
the law is the completed OLD cutoff law, and the lower-right true-frame mean
block is bounded below by the identity. -/
theorem main_inverse_heat_initial_ge_two (M : ABKModel 2) (m n : ℤ) :
    2 ≤ mainInverseHeatAverage n M m 0 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let ν := Cutoff.coefficientCutoffLaw M m
  let Q := originCube 2 n
  let σ := (Annealed.sigmaBar M m : ℝ)
  let F : RegCoeffField 2 → ℝ := fun a =>
    σ * Matrix.trace (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight
  have hentry := Provider.Annealed.coefficientCutoffLaw_integrable_blockMatEntry_coarseBlockMatrix
    M m Q
  have hF : Integrable F ν := by
    have hsum : Integrable (fun a : RegCoeffField 2 =>
        ∑ i : Fin 2, σ * blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun)
          (Sum.inr i) (Sum.inr i)) ν := by
      exact integrable_finsetSum Finset.univ (fun i _ =>
        (hentry (Sum.inr i) (Sum.inr i)).const_mul σ)
    refine hsum.congr ?_
    filter_upwards [] with a
    simp [F, Matrix.trace, blockMatEntry, Q]; ring
  have hmap : Measure.map (Cutoff.coefficientCutoff M.nu m) μ = ν :=
    mainInsertion_old_law M m
  have hsource : ∀ ω : Cutoff.CutoffSample 2,
      mainInsertionInverseTrace M m n 0 ω = F (Cutoff.coefficientCutoff M.nu m ω) := by
    intro ω
    have hcoeff : Model.partialInsertedCoefficient M m 0 ω =
        Cutoff.coefficientCutoff M.nu m ω := by
      ext x i j
      simp [Model.partialInsertedCoefficient, RegCoeffField.add_apply, RegCoeffField.smul_apply]
    rw [mainInsertionInverseTrace, hcoeff]
  have hstart : mainInverseHeatAverage n M m 0 = ∫ a, F a ∂ν := by
    unfold mainInverseHeatAverage
    calc
      _ = ∫ ω, F (Cutoff.coefficientCutoff M.nu m ω) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hsource
      _ = ∫ a, F a ∂ν := by
        rw [← hmap]
        exact (integral_map (Cutoff.measurable_coefficientCutoff M.nu m).aemeasurable
          hF.aestronglyMeasurable).symm
  obtain ⟨α, β, hα, hβ, hmean⟩ :=
    ASDExplicitGamma.Variational.exists_trueFrame_mean_scalars M m n
  have hframe := hmean 0
  rw [translateSet_zero] at hframe
  have hFmean : (∫ a, F a ∂ν) = 2 * β := by
    have hentryIntegral (i : Fin 2) :
        (∫ a : RegCoeffField 2,
          blockMatEntry (Variational.frameMatrix σ (coarseBlockMatrix (cubeSet Q) a.toFun))
            (Sum.inr i) (Sum.inr i) ∂ν) =
        blockMatEntry (Variational.frameMatrix σ
          (Ch04.annealedBlockMatrix ν (cubeSet Q))) (Sum.inr i) (Sum.inr i) := by
      simpa only [Q] using
        Variational.integral_frameMatrix_entry M m (cubeSet Q) σ (Sum.inr i) (Sum.inr i)
    calc
      _ = ∑ i : Fin 2, ∫ a : RegCoeffField 2,
          blockMatEntry (Variational.frameMatrix σ (coarseBlockMatrix (cubeSet Q) a.toFun))
            (Sum.inr i) (Sum.inr i) ∂ν := by
        calc
          _ = ∫ a, ∑ i : Fin 2,
              blockMatEntry (Variational.frameMatrix σ (coarseBlockMatrix (cubeSet Q) a.toFun))
                (Sum.inr i) (Sum.inr i) ∂ν := by
            apply integral_congr_ae
            filter_upwards [] with a
            simp [F, Variational.frameMatrix, Matrix.trace, blockMatEntry, σ, Q]; ring
          _ = _ := integral_finsetSum _ (fun i _ =>
            Variational.integrable_frameMatrix_entry M m Q σ
              (Sum.inr i) (Sum.inr i))
      _ = ∑ i : Fin 2,
          blockMatEntry (Variational.frameMatrix σ
            (Ch04.annealedBlockMatrix ν (cubeSet Q))) (Sum.inr i) (Sum.inr i) := by
        exact Finset.sum_congr rfl (fun i _ => hentryIntegral i)
      _ = 2 * β := by
        rw [hframe]
        simp [Ch02.blockDiag, blockMatEntry]
  rw [hstart, hFmean]
  nlinarith

end ASDExplicitGamma.Main
