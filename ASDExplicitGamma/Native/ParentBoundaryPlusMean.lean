module

public import ASDExplicitGamma.Native.ParentBoundaryCovarianceRotation

/-! The actual complete positive covariance mean and full flat trace
retain their physical b² baseline after own-native Gram centering. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- Centering never removes the genuine fresh-field flat trace charge.
The exact Bflat is 2b²-2Y and is bounded above by 2b². -/
theorem parent_boundary_flat_baseline (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    oldSignedFlatBoundaryEnergy Q b L=2*b^2-2*parentBoundaryDirichletEnergy Q b L ∧
    oldSignedFlatBoundaryEnergy Q b L≤2*b^2 := by
  have he := (old_signed_flat_boundary_energy_trace Q b L).tsum_eq
  change oldSignedFlatBoundaryEnergy Q b L=2*(b^2-parentBoundaryDirichletEnergy Q b L) at he
  have hY := (parent_boundary_dirichlet_energy_bounds Q b L).1
  constructor <;> linarith only [he,hY]

end
end ASDExplicitGamma.Native
