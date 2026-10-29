module

public import ASDExplicitGamma.Scalar.OldHessianTrialCovarianceReceiver
public import ASDExplicitGamma.Scalar.OldHessianTrialCovarianceSpatial

/-! Actual cell-dependent Eminus reciprocal fields, before scalar payment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual reciprocal TOP field at each deterministic Eminus column,
measured in its own fine cell's complete weak norm. -/
def oldHessianCovarianceReceiverTerm (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (i : Fin 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  oldHessianCovarianceSpatialReceiver (originCube 2 (m+129)) 134 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω) b L i

/-- Each varying deterministic Eminus column is retained inside its actual
local response. The full physical receiver is bounded by its proved envelope. -/
theorem old_hessian_actual_covariance_receiver_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (∑ i : Fin 2,oldHessianCovarianceReceiverTerm M m b L i ω)≤
        oldHessianCovarianceReceiverEnvelope M m b L ω := by
  let Q := originCube 2 (m+129)
  let q := fun (i : Fin 2) (U : OldSignedCellIndex Q 134) =>
    matVecMul (oldHessianMeanCovarianceError Q U.val b L) (basisVec i)
  have hall := ae_all_iff.mpr (fun i : Fin 2 => ae_all_iff.mpr (fun U : OldSignedCellIndex Q 134 =>
    old_hessian_actual_cell_top_directional_join M h hM hg N hpast m hm U.val U.property (q i U)))
  filter_upwards [hall] with ω hω
  apply Finset.sum_le_sum
  intro i _
  apply old_signed_cell_average_mono
  intro U
  exact (le_add_of_nonneg_left (vectorWeakHaarEnergy_nonneg U.val _)).trans (hω i U)

end
end ASDExplicitGamma.Scalar
