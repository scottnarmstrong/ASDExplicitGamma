module

public import ASDExplicitGamma.Scalar.DefectEnergyModalInputs
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! A continuous potential-from-gradient map on a cube: a left inverse of the (injective,
closed-range) gradient of the closed `H¹₀` graph space. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory

theorem exists_potential_map (Q : TriadicCube 2) :
    ∃ P : HilbertVectorL2 (openCubeSet Q) →L[ℝ] H10GraphClosedSpace (openCubeSet Q),
      ∀ z, P (H10GraphClosed.gradientCLM z) = z := by
  have hU := isOpenBoundedConvexDomain_openCubeSet Q
  obtain ⟨K, hK⟩ := H10GraphClosed.exists_antilipschitzWith_gradientCLM (U := openCubeSet Q) hU
  have hinj := hK.injective
  have hclo := H10GraphClosed.isClosed_range_gradientCLM (U := openCubeSet Q) hU
  let g := H10GraphClosed.gradientCLM (d := 2) (U := openCubeSet Q)
  letI : CompleteSpace (LinearMap.range g.toLinearMap) := by
    have : CompleteSpace (Set.range g) := hclo.completeSpace_coe
    exact this
  let e := g.equivRange hinj hclo
  let Pr := (LinearMap.range g.toLinearMap).orthogonalProjectionOnto
  refine ⟨(e.symm : (LinearMap.range g.toLinearMap) →L[ℝ] _).comp Pr, fun z => ?_⟩
  have hz : (⟨g z, g.mem_range_self z⟩ : LinearMap.range g.toLinearMap) = e z := rfl
  have h1 : Pr (g z) = e z := by
    rw [← hz]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := LinearMap.range g.toLinearMap)
      ⟨g z, g.mem_range_self z⟩
  change e.symm (Pr (g z)) = z
  rw [h1]
  exact e.symm_apply_apply z

end ASDExplicitGamma.Scalar
