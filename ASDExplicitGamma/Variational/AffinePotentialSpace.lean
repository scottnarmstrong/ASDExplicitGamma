module

public import ASDExplicitGamma.Triadic.DiagLinear
public import Homogenization.Sobolev.H1.Algebra.Membership
public import Homogenization.Sobolev.Foundations.H10Graph

/-! The literal linear space of affine-boundary H1 potentials and its gradient map. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

local instance affinePotentialFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

 def zeroTracePotentialSubmodule (U : Set (Vec 2)) : Submodule ℝ (H1Function U) where
  carrier := {v | ∃ r : H10Function U, r.toH1Function = v}
  zero_mem' := ⟨0,rfl⟩
  add_mem' := by
    rintro f g ⟨u,hu⟩ ⟨v,hv⟩
    exact ⟨u+v,congrArg₂ (·+·) hu hv⟩
  smul_mem' := by
    rintro c f ⟨u,hu⟩
    exact ⟨c • u,congrArg (c • ·) hu⟩

 def affinePotentialSubmodule (Q : TriadicCube 2) : Submodule ℝ (H1Function (openCubeSet Q)) :=
  LinearMap.range (diagAffineLinear Q) ⊔ zeroTracePotentialSubmodule (openCubeSet Q)

 def h1GradientLinearMap (U : Set (Vec 2)) : H1Function U →ₗ[ℝ] HilbertVectorL2 U where
  toFun := H1Function.gradToHilbertVectorL2
  map_add' := H1Function.gradToHilbertVectorL2_add
  map_smul' := H1Function.gradToHilbertVectorL2_smul

 def h1ValueLinearMapL2 (U : Set (Vec 2)) : H1Function U →ₗ[ℝ] ScalarL2 U where
  toFun := H1Function.toScalarL2
  map_add' := H1Function.toScalarL2_add
  map_smul' := H1Function.toScalarL2_smul

 def affineGradientSubmodule (Q : TriadicCube 2) : Submodule ℝ (HilbertVectorL2 (openCubeSet Q)) :=
  (affinePotentialSubmodule Q).map (h1GradientLinearMap (openCubeSet Q))

 theorem mem_affinePotentialSubmodule (Q : TriadicCube 2) (p : Vec 2) (r : H10Function (openCubeSet Q)) :
    lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r ∈ affinePotentialSubmodule Q := by
  apply Submodule.add_mem_sup
  · exact ⟨p,rfl⟩
  · exact ⟨r,rfl⟩

end
end ASDExplicitGamma.Variational
