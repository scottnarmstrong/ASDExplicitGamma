module

public import ASDExplicitGamma.Native.ParentBoundaryMinusBeta
public import ASDExplicitGamma.Native.ParentBoundarySourceClock
public import ASDExplicitGamma.Native.ParentBoundaryBetaAlgebra

/-! Substitution of the physical own-native Dirichlet clock into the
complete centered fine-cell covariance estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- The dimensionless minus covariance clock on independent comparison
cells. Its shell amplitude is factored out only after the complete
physical covariance and its parent Gram mean have been identified. -/
theorem parent_boundary_minus_beta_clock (m : ℤ) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0<l})
    (hscale : 3*cubeScaleFactor (originCube 2 m)≤L.1) :
    let R := cubeScaleFactor (originCube 2 m)
    let rho := (26/15:ℝ)*(R/L.1)^2
    descendantsAverage (originCube 2 m) depth (fun U =>
      parentBoundaryCenteredBeta (originCube 2 m) U b L false^2) ≤
      b^4*(rho-rho^2/2+planarC1^2*(156/5:ℝ)*
        (R/(3^depth*L.1))^2*(1+Real.sqrt (rho/2))^2) := by
  dsimp only
  let Q := originCube 2 m
  let R := cubeScaleFactor Q
  let rho := (26/15:ℝ)*(R/L.1)^2
  let Y := parentBoundaryDirichletEnergy Q b L
  have hr := parent_boundary_rho_bounds R L.1 (Triadic.cubeScaleFactor_pos' Q).le L.2 hscale
  have hy0 := (parent_boundary_dirichlet_energy_bounds Q b L).1
  have hy : Y≤b^2*rho := by
    simpa only [Y,rho,R,mul_comm] using parent_boundary_dirichlet_energy_rational_clock Q b L
  have hv := parent_boundary_value_variance_clock (b^2) Y rho (sq_nonneg _) hy0 hy hr.1 hr.2
  have hg := parent_boundary_covariance_gradient_clock (b^2) (mainFlatSigmaSq b L) Y rho
    (sq_nonneg _) (by unfold mainFlatSigmaSq; positivity) hy hr.1
  apply (parent_boundary_minus_beta_squared m depth b L).trans
  apply (add_le_add hv (mul_le_mul_of_nonneg_left hg (by positivity))).trans_eq
  unfold mainFlatSigmaSq
  simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
  dsimp only [rho,R,Q]
  ring

end
end ASDExplicitGamma.Native
