module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalFrame
public import ASDExplicitGamma.Scalar.UpperCellEnergyOldMatrixMean
public import ASDExplicitGamma.Scalar.TrueFrameNormalization

/-! The OLD inverse trace is integrable and its true-frame mean is at least two. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
noncomputable section

/-- The actual normalized inverse trace of the OLD parent response is integrable
on the original sample space and has mean at least two, by true-frame normalization. -/
theorem old_hessian_inverse_trace_mean (M : ABKModel 2) (m : ℤ) :
    Integrable (fun ω => Matrix.trace (coarseBlockMatrix (openCubeSet (originCube 2 (m+129)))
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω))).lowerRight) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    2≤∫ ω,Matrix.trace (coarseBlockMatrix (openCubeSet (originCube 2 (m+129)))
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω))).lowerRight ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  have he (ω : Cutoff.CutoffSample 2) : Matrix.trace (coarseBlockMatrix (openCubeSet (originCube 2 (m+129)))
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m:ℝ) (oldHessianOldOpenCoefficient (m+129) m ω))).lowerRight=
      ∑ i : Fin 2,blockMatEntry (frameMatrix (Annealed.sigmaBar M m:ℝ) (coarseBlockMatrix (cubeSet (originCube 2 (m+129)))
        (Cutoff.coefficientCutoff M.nu m ω).toFun)) (Sum.inr i) (Sum.inr i) := by
    rw [old_hessian_old_open_coarse_frame M (m+129) m ω (originCube 2 (m+129)) subset_rfl]
    rfl
  simp_rw [he]
  have hint (i : Fin 2) := upper_cell_old_framed_entry_integrable M m (originCube 2 (m+129)) (Annealed.sigmaBar M m:ℝ) (Sum.inr i) (Sum.inr i)
  have hval (i : Fin 2) := upper_cell_old_framed_entry_integral M m (originCube 2 (m+129)) (Annealed.sigmaBar M m:ℝ) (Sum.inr i) (Sum.inr i)
  refine ⟨integrable_finsetSum _ (fun i _ => hint i),?_⟩
  rw [integral_finset_sum _ (fun i _ => hint i)]
  simp_rw [hval]
  have hone (i : Fin 2) : 1≤blockMatEntry (frameMatrix (Annealed.sigmaBar M m:ℝ) (Book.Ch04.annealedBlockMatrix
      (Cutoff.coefficientCutoffLaw M m) (cubeSet (originCube 2 (m+129))))) (Sum.inr i) (Sum.inr i) := by
    have hh := true_frame_mean_excess_nonneg M m (originCube 2 (m+129)) (blockBasis (Sum.inr i))
    rw [blockBasis_pairing] at hh
    have h1 : blockVecDot (blockBasis (Sum.inr i : BlockCoord 2)) (blockBasis (Sum.inr i)) = 1 := by
      simp [blockBasis,blockVecDot,vecDot_single_left,vecDot_zero_left]
    linarith
  calc (2:ℝ) = ∑ i : Fin 2,(1:ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hone i)

end
end ASDExplicitGamma.Scalar
