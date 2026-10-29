module

public import ASDExplicitGamma.Variational.AffinePotentialSpace
public import Homogenization.Sobolev.PotentialSolenoidalExact

/-! Closedness of the actual affine-boundary gradient space, without a closure surrogate. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory
noncomputable section

 theorem potentialZeroTrace_eq_range_gradient (Q : TriadicCube 2) :
    (PotentialSolenoidalExact.potentialZeroTrace (openCubeSet Q) : Set (HilbertVectorL2 (openCubeSet Q))) =
      Set.range (H10GraphClosed.gradientCLM (U := openCubeSet Q)) := by
  ext F
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨⟨(u.toH1Function.toScalarL2,u.toH1Function.gradToHilbertVectorL2),
      (Submodule.le_topologicalClosure _) (h10_pair_mem_h10GraphSubmodule u)⟩,?_⟩
    exact hu
  · rintro ⟨z,rfl⟩
    obtain ⟨u,_,hg⟩ := exists_h10Function_of_mem_h10GraphClosedSubmodule
      (isOpenBoundedConvexDomain_openCubeSet Q) z.property
    exact ⟨u,hg⟩

 theorem potentialZeroTrace_isClosed (Q : TriadicCube 2) :
    IsClosed (PotentialSolenoidalExact.potentialZeroTrace (openCubeSet Q) : Set (HilbertVectorL2 (openCubeSet Q))) := by
  rw [potentialZeroTrace_eq_range_gradient]
  exact H10GraphClosed.isClosed_range_gradientCLM (isOpenBoundedConvexDomain_openCubeSet Q)

 theorem affineGradientSubmodule_eq (Q : TriadicCube 2) :
    affineGradientSubmodule Q = LinearMap.range ((h1GradientLinearMap (openCubeSet Q)).comp (Triadic.diagAffineLinear Q)) ⊔
      PotentialSolenoidalExact.potentialZeroTrace (openCubeSet Q) := by
  unfold affineGradientSubmodule affinePotentialSubmodule
  rw [Submodule.map_sup, ← LinearMap.range_comp]
  congr 1
  ext F
  constructor
  · rintro ⟨v,⟨r,hr⟩,hv⟩
    exact ⟨r,by simpa only [← hr, h1GradientLinearMap, LinearMap.coe_mk, AddHom.coe_mk] using hv⟩
  · rintro ⟨r,hr⟩
    exact ⟨r.toH1Function,⟨r,rfl⟩,hr⟩

 theorem affineGradientSubmodule_isClosed (Q : TriadicCube 2) :
    IsClosed (affineGradientSubmodule Q : Set (HilbertVectorL2 (openCubeSet Q))) := by
  rw [affineGradientSubmodule_eq, sup_comm]
  exact Submodule.isClosed_sup_finiteDimensional _ _ (potentialZeroTrace_isClosed Q)

/-- The source's closed first-component space, with proved literal-gradient semantics. -/
def affineGradientClosedSubmodule (Q : TriadicCube 2) : ClosedSubmodule ℝ (HilbertVectorL2 (openCubeSet Q)) :=
  ⟨affineGradientSubmodule Q,affineGradientSubmodule_isClosed Q⟩

end
end ASDExplicitGamma.Variational
