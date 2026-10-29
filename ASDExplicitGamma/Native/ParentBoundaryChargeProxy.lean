module

public import ASDExplicitGamma.Native.ParentBoundaryBrokenBudgets
public import ASDExplicitGamma.Native.ParentBoundaryBetaClock

/-! The boundary-fixed two-root charge on the actual comparison cells,
with a complete shifted trace proxy for the same parent minimizers. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational Inverse
noncomputable section

/-- Spatial Cauchy retains the actual normalized descendant weights. -/
theorem parent_boundary_descendant_cauchy (Q : TriadicCube 2) (depth : ℕ)
    (f g : TriadicCube 2 → ℝ)
    (hf : ∀ U ∈ descendantsAtDepth Q depth,0≤f U)
    (hg : ∀ U ∈ descendantsAtDepth Q depth,0≤g U) :
    descendantsAverage Q depth (fun U => f U*g U) ≤
      Real.sqrt (descendantsAverage Q depth (fun U => f U^2))*
        Real.sqrt (descendantsAverage Q depth (fun U => g U^2)) := by
  have hh := descendantsAverage_mul_le_Lp_mul_Lq_of_nonneg Q depth f g
    Real.HolderConjugate.two_two hf hg
  simpa only [Real.rpow_two,←Real.sqrt_eq_rpow] using hh

end
end ASDExplicitGamma.Native
