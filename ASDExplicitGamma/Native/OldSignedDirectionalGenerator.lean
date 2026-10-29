module

public import ASDExplicitGamma.Native.OldSignedCanonicalTrialAssembly
public import ASDExplicitGamma.Native.OldSignedDirectionalTrialTotalBound
public import ASDExplicitGamma.Native.OldSignedPhysicalTraceSeries

/-! The physical four-load OLD signed generator AN (5.3). Every term is
constructed from the actual coefficient, and all complete sums converge. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian
noncomputable section

/-- Directional refinement of AN (5.3) for the actual physical canonical OLD Hessians. The signed
inverse-trace term is retained without any positivity assumption on it.
There are no assumed local, covariance, projection or generator estimates. -/
theorem native_boundary_old_signed_generator_directional (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 m
    let a := responseFramePlanarCoefficientField nu sigma k
    let f := fun n : whiteBasisIndex => ∑ c : BlockCoord 2,
      oldSignedPhysicalHessian Q nu sigma hnu hsigma k (blockBasis c) b L n
    Summable f ∧ (∑' n,f n)≤oldSignedFlatBoundaryEnergy Q b L+
      oldSignedFlatAffineContribution Q mesh a b L-
      b^2*(Matrix.trace (coarseBlockMatrix (openCubeSet Q) a).lowerRight-2)+
      descendantsAverage Q mesh (fun U => oldSignedDirectionalCellError Q U mesh nu sigma hnu hsigma k b L) := by
  intro Q a f
  have hs := old_signed_physical_trace_summable m nu sigma hnu hsigma k b L
  have ht := old_signed_trial_total_bound_directional m mesh nu sigma hnu hsigma k b L
  exact ⟨hs,(hs.tsum_le_tsum (fun n =>
    old_signed_canonical_hessian_le_trial_total Q mesh nu sigma hnu hsigma k b L n) ht.1).trans ht.2⟩

end
end ASDExplicitGamma.Native
