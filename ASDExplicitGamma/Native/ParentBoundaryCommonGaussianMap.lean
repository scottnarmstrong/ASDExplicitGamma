module

public import ASDExplicitGamma.Native.ParentBoundaryCommonCubeCarrier
public import ASDExplicitGamma.Native.ParentBoundaryCommonResponseDirections
public import ASDExplicitGamma.Inverse.PureFluxGeneratorQ3Map

/-! Literal Gaussian-series map into the common-centered observed coefficient. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic
noncomputable section

local instance parentCommonGaussianMapCompact (P : TriadicCube 2) : CompactSpace (closure (cubeSet P)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet P).isCompact_closure

/-- Restrict one enclosing Gaussian cube field to the original source square. -/
def parentBoundaryCommonEnclosingRestriction (P : TriadicCube 2) (ell : ℤ)
    (hP : closure (cubeSet P) ⊆ openCubeSet (originCube 2 ell)) :
    C(closure (cubeSet (originCube 2 ell)),ℝ) →L[ℝ] C(closure (cubeSet P),ℝ) :=
  ContinuousMap.compCLM ℝ ℝ
    ⟨fun x => ⟨x.val,subset_closure (openCubeSet_subset_cubeSet _ (hP x.property))⟩,
      continuous_subtype_val.subtype_mk _⟩

/-- The literal common-center observed response map, before applying a
Gaussian realization. The same source center is used for every descendant. -/
def parentBoundaryCommonObservedMap {P Q : TriadicCube 2} {d : ℕ}
    (hQ : Q ∈ descendantsAtDepth P d) :
    C(closure (cubeSet P),ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q) :=
  (parentBoundaryCommonOpenCellCoefficient hQ).comp
    (centeringMap (parentBoundaryCommonCubeCenter P))

/-- Every canonical enclosing-cube Gaussian direction is EXACTLY the actual
common-center response direction, with no covariance-law premise. -/
theorem parent_boundary_common_gaussian_directions_eq
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (ell : ℤ) (hP : closure (cubeSet P) ⊆ openCubeSet (originCube 2 ell))
    (b : ℝ) (L : {l : ℝ // 0 < l}) (j : ℕ) :
    parentBoundaryCommonObservedMap hQ (parentBoundaryCommonEnclosingRestriction P ell hP
      (pureFluxMainCubeQ3Directions ell b L j)) =
      parentBoundaryCommonResponseDirections P Q b L j := by
  ext x
  simp [parentBoundaryCommonObservedMap,parentBoundaryCommonOpenCellCoefficient,
    BoundedContinuousFunction.compContinuousCLM_apply,BoundedContinuousFunction.compContinuous_apply,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply,centeringMap_apply,
    parentBoundaryCommonEnclosingRestriction,pureFluxMainCubeQ3Directions,
    mainCubeH3Value_direction,parentBoundaryCommonCubeCenter,
    parentBoundaryCommonResponseDirections,squareQ3Directions,mainShellResponseCoefficient]
  rfl

/-- The physical common-center family is the bounded image of one genuine
square-summable Hilbert Gaussian realization. This identifies its complete
power trace with the actual canonical shell, not a truncated approximation. -/
theorem parent_boundary_common_gaussian_factor
    {P Q : TriadicCube 2} {d : ℕ} (hQ : Q ∈ descendantsAtDepth P d)
    (ell : ℤ) (hP : closure (cubeSet P) ⊆ openCubeSet (originCube 2 ell))
    (b : ℝ) (L : {l : ℝ // 0 < l}) :
    ∃ T : MainCubeH3 ell b L →L[ℝ] ResponseCoefficient (openCubeSet Q),
      ∀ j,T (mainCubeQ3Directions ell b L j)=parentBoundaryCommonResponseDirections P Q b L j := by
  refine ⟨(parentBoundaryCommonObservedMap hQ).comp
    ((parentBoundaryCommonEnclosingRestriction P ell hP).comp (mainCubeH3Value ell b L)),?_⟩
  intro j
  exact parent_boundary_common_gaussian_directions_eq hQ ell hP b L j

end
end ASDExplicitGamma.Native
