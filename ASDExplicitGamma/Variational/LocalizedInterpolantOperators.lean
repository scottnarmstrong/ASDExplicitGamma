module

public import ASDExplicitGamma.Variational.BoundedGradientFactor

/-! The two source interpolation bounds produce unique operators on actual affine gradients. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization
noncomputable section

 def interpolantGradientLinear (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) :
    affinePotentialSubmodule Q →ₗ[ℝ] HilbertVectorL2 (openCubeSet Q) :=
  ((h1GradientLinearMap (openCubeSet Q)).comp I).comp (affinePotentialSubmodule Q).subtype

 def interpolantResidualLinear (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) :
    affinePotentialSubmodule Q →ₗ[ℝ] ScalarL2 (openCubeSet Q) :=
  ((h1ValueLinearMapL2 (openCubeSet Q)).comp (LinearMap.id-I)).comp (affinePotentialSubmodule Q).subtype

 theorem existsUnique_interpolantGradientOperator (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) {A : ℝ} (hA : 0 ≤ A)
    (hI : ∀ v ∈ affinePotentialSubmodule Q, ‖(I v).gradToHilbertVectorL2‖ ≤ A*‖v.gradToHilbertVectorL2‖) :
    ∃! L : affineGradientClosedSubmodule Q →L[ℝ] HilbertVectorL2 (openCubeSet Q),
      ‖L‖ ≤ A ∧ ∀ v : affinePotentialSubmodule Q,
        L (affineGradientRangeMap Q v)=(I v).gradToHilbertVectorL2 := by
  exact existsUnique_bounded_factor (affineGradientRangeMap Q) (affineGradientRangeMap_surjective Q)
    (interpolantGradientLinear Q I) hA (fun v => hI v v.property)

 theorem existsUnique_interpolantResidualOperator (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) {B : ℝ} (hB : 0 ≤ B)
    (hI : ∀ v ∈ affinePotentialSubmodule Q, ‖(v-I v).toScalarL2‖ ≤ B*‖v.gradToHilbertVectorL2‖) :
    ∃! L : affineGradientClosedSubmodule Q →L[ℝ] ScalarL2 (openCubeSet Q),
      ‖L‖ ≤ B ∧ ∀ v : affinePotentialSubmodule Q,
        L (affineGradientRangeMap Q v)=(v-I v).toScalarL2 := by
  exact existsUnique_bounded_factor (affineGradientRangeMap Q) (affineGradientRangeMap_surjective Q)
    (interpolantResidualLinear Q I) hB (fun v => hI v v.property)

 def interpolantGradientOperator (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) {A : ℝ} (hA : 0 ≤ A)
    (hI : ∀ v ∈ affinePotentialSubmodule Q, ‖(I v).gradToHilbertVectorL2‖ ≤ A*‖v.gradToHilbertVectorL2‖) :
    affineGradientClosedSubmodule Q →L[ℝ] HilbertVectorL2 (openCubeSet Q) :=
  Classical.choose (existsUnique_interpolantGradientOperator Q I hA hI)

 def interpolantResidualOperator (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) {B : ℝ} (hB : 0 ≤ B)
    (hI : ∀ v ∈ affinePotentialSubmodule Q, ‖(v-I v).toScalarL2‖ ≤ B*‖v.gradToHilbertVectorL2‖) :
    affineGradientClosedSubmodule Q →L[ℝ] ScalarL2 (openCubeSet Q) :=
  Classical.choose (existsUnique_interpolantResidualOperator Q I hB hI)

 theorem interpolantGradientOperator_spec (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) {A : ℝ} (hA : 0 ≤ A)
    (hI : ∀ v ∈ affinePotentialSubmodule Q, ‖(I v).gradToHilbertVectorL2‖ ≤ A*‖v.gradToHilbertVectorL2‖) :
    ‖interpolantGradientOperator Q I hA hI‖ ≤ A ∧ ∀ v : affinePotentialSubmodule Q,
      interpolantGradientOperator Q I hA hI (affineGradientRangeMap Q v)=(I v).gradToHilbertVectorL2 :=
  (Classical.choose_spec (existsUnique_interpolantGradientOperator Q I hA hI)).1

 theorem interpolantResidualOperator_spec (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) {B : ℝ} (hB : 0 ≤ B)
    (hI : ∀ v ∈ affinePotentialSubmodule Q, ‖(v-I v).toScalarL2‖ ≤ B*‖v.gradToHilbertVectorL2‖) :
    ‖interpolantResidualOperator Q I hB hI‖ ≤ B ∧ ∀ v : affinePotentialSubmodule Q,
      interpolantResidualOperator Q I hB hI (affineGradientRangeMap Q v)=(v-I v).toScalarL2 :=
  (Classical.choose_spec (existsUnique_interpolantResidualOperator Q I hB hI)).1

end
end ASDExplicitGamma.Variational
