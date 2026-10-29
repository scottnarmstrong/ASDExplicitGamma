module

public import ASDExplicitGamma.Native.ParentBoundaryTrialAssembly
public import ASDExplicitGamma.Native.ParentBoundaryDirectionalTrialBound
public import ASDExplicitGamma.Native.OldSignedPhysicalTraceSeries

/-! The physical four-load OLD signed generator AN (5.3). Every term is
constructed from the actual coefficient, and all complete sums converge. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- AN (5.3) for the actual physical canonical OLD Hessians. The signed
inverse-trace term is retained without any positivity assumption on it.
There are no assumed local, covariance, projection or generator estimates. -/
theorem parent_boundary_directional_signed_generator (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 m
    let a := responseFramePlanarCoefficientField nu sigma k
    let f := fun n : whiteBasisIndex => ∑ c : BlockCoord 2,
      oldSignedPhysicalHessian Q nu sigma hnu hsigma k (blockBasis c) b L n
    Summable f ∧ (∑' n,f n)≤oldSignedFlatBoundaryEnergy Q b L+
      oldSignedFlatAffineContribution Q mesh a b L-
      parentBoundaryDirichletEnergy Q b L*(Matrix.trace (coarseBlockMatrix (openCubeSet Q) a).lowerRight-2)+
      descendantsAverage Q mesh (fun U => parentBoundaryDirectionalCellError Q U nu sigma hnu hsigma k b L) := by
  intro Q a f
  have hs := old_signed_physical_trace_summable m nu sigma hnu hsigma k b L
  have ht := parent_boundary_trial_directional_bound m mesh nu sigma hnu hsigma k b L
  exact ⟨hs,(hs.tsum_le_tsum (fun n =>
    parent_boundary_canonical_hessian_le_trial_total Q mesh nu sigma hnu hsigma k b L n) ht.1).trans ht.2⟩

end
end ASDExplicitGamma.Native
