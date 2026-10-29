module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterDistance
public import ASDExplicitGamma.Native.VanishingBracketOverlap
public import ASDExplicitGamma.Native.ParentBoundaryBandCellMoments

/-! Actual full white-noise common-center directions restricted to a child,
with the exact response-frame link constructed rather than assumed. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Gaussian Triadic Variational Main
open scoped ENNReal
noncomputable section

local instance parentCommonPhysicalCompact (Q : TriadicCube 2) : CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

/-- Literal restriction from the common closed source field to the open
child response carrier. The field, not merely its law, is restricted. -/
def parentBoundaryCommonOpenCellCoefficient {P Q : TriadicCube 2} {d : ℕ}
    (hQ : Q ∈ descendantsAtDepth P d) :
    C(closure (cubeSet P),ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    ⟨fun x => ⟨x.val, closure_mono
      (fun y hy => cubeSet_subset_of_mem_descendantsAtDepth hQ (openCubeSet_subset_cubeSet Q hy)) x.property⟩,
      continuous_subtype_val.subtype_mk _⟩).comp
    (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet P)) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap

/-- The restricted response coefficient has the exact original scalar value. -/
theorem parent_boundary_common_open_cell_coefficient_value
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (f : C(closure (cubeSet P),ℝ)) {x : Vec 2} (hx : x ∈ openCubeSet Q) :
    responseCoefficientExtension (parentBoundaryCommonOpenCellCoefficient hQ f) x =
      f ⟨x,subset_closure (cubeSet_subset_of_mem_descendantsAtDepth hQ (openCubeSet_subset_cubeSet Q hx))⟩ := by
  rw [responseCoefficientExtension_eq _ hx]
  simp [parentBoundaryCommonOpenCellCoefficient,
    BoundedContinuousFunction.compContinuousCLM_apply,ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]

end
end ASDExplicitGamma.Native
