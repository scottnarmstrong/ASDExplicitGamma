module

public import ASDExplicitGamma.Scalar.OldHessianTrialParentWeakTheta

/-! The same two actual bottom loads share one parent primal/reciprocal budget. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Joint first and reciprocal defects of the two original bottom loads. -/
def oldHessianBottomPairedCellEnergy (Q U : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) : ℝ :=
  ∑ c : BlockCoord 2,vectorWeakHaarEnergy U (oldSignedPairedDefectField Q nu sigma hnu hsigma k true c)

/-- Their intrinsic physical parent energy on the unchanged fine tiling. -/
def oldHessianParentBottomPairEnergy (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 (m+129)
  oldSignedCellAverage Q 134 (fun U => oldHessianBottomPairedCellEnergy Q U.val M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω))

/-- The two bottom primal and reciprocal errors cost one OLD proxy, with
no factor-two loss from replacing them by the full four-load error profiles. -/
theorem old_hessian_actual_parent_bottom_pair_le_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      oldHessianParentBottomPairEnergy M m ω≤oldHessianGroupedOldTheta M m ω := by
  filter_upwards [old_hessian_actual_parent_weak_trace_le_theta M h hM hg N hpast m hm] with ω hω
  have hh := old_signed_tiled_paired_weak_trace_bound (originCube 2 (m+129)) 134 M.nu
    (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (oldHessianOldOpenCoefficient (m+129) m ω) true
  change oldSignedCellAverage (originCube 2 (m+129)) 134 _≤_
  rw [old_signed_cell_average_eq_descendantsAverage (originCube 2 (m+129)) 134
    (fun U => oldHessianBottomPairedCellEnergy (originCube 2 (m+129)) U M.nu (Annealed.sigmaBar M m) M.nu_pos
      (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω))]
  exact hh.trans hω

end
end ASDExplicitGamma.Scalar
