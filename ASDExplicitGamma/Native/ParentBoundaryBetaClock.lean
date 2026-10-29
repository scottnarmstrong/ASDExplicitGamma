module

public import ASDExplicitGamma.Native.ParentBoundaryBetaRotation
public import ASDExplicitGamma.Native.ParentBoundaryMinusBetaClock

/-! One physical centered covariance clock controls both signs. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- Dimensionless own-native covariance clock. -/
def parentBoundaryCovarianceClock (R : ℝ) (depth : ℕ) (L : ℝ) : ℝ :=
  let rho := (26/15:ℝ)*(R/L)^2
  rho-rho^2/2+planarC1^2*(156/5:ℝ)*(R/(3^depth*L))^2*(1+Real.sqrt (rho/2))^2

/-- Both actual centered contraction signs obey the sharp squared clock
on the same independent fine partition. -/
theorem parent_boundary_centered_beta_clock_squared (m : ℤ) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool)
    (hscale : 3*cubeScaleFactor (originCube 2 m)≤L.1) :
    descendantsAverage (originCube 2 m) depth (fun U =>
      parentBoundaryCenteredBeta (originCube 2 m) U b L plus^2) ≤
      b^4*parentBoundaryCovarianceClock (cubeScaleFactor (originCube 2 m)) depth L.1 := by
  have he : descendantsAverage (originCube 2 m) depth (fun U =>
      parentBoundaryCenteredBeta (originCube 2 m) U b L plus^2) =
      descendantsAverage (originCube 2 m) depth (fun U =>
        parentBoundaryCenteredBeta (originCube 2 m) U b L false^2) := by
    apply congrArg (fun z : ℝ => ((descendantsAtDepth (originCube 2 m) depth).card : ℝ)⁻¹*z)
    apply Finset.sum_congr rfl
    intro U hU
    cases plus
    · rfl
    · rw [parent_boundary_centered_beta_rotation (originCube 2 m) U depth hU]
  rw [he]
  exact parent_boundary_minus_beta_clock m depth b L hscale

/-- Root mean square beta estimate for the actual complete
common-noise covariance. The physical variance is b². -/
theorem parent_boundary_centered_beta_clock (m : ℤ) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l}) (plus : Bool)
    (hscale : 3*cubeScaleFactor (originCube 2 m)≤L.1) :
    Real.sqrt (descendantsAverage (originCube 2 m) depth (fun U =>
      parentBoundaryCenteredBeta (originCube 2 m) U b L plus^2)) ≤
      b^2*Real.sqrt (parentBoundaryCovarianceClock (cubeScaleFactor (originCube 2 m)) depth L.1) := by
  apply (Real.sqrt_le_sqrt (parent_boundary_centered_beta_clock_squared m depth b L plus hscale)).trans_eq
  rw [show b^4=(b^2)^2 by ring,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (sq_nonneg b)]

end
end ASDExplicitGamma.Native
