module

public import ASDExplicitGamma.Native.ParentBoundaryDirichletSymmetry
public import ASDExplicitGamma.Native.OldSignedDirichletLoadSymmetry

/-! Actual complete-white linear operators for the raw source and its
parent Dirichlet projection, retaining physical spatial representatives. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Scalar
noncomputable section

local instance parentBoundaryLoadFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Complete-white source operator, in the genuine physical vector L2 space. -/
def parentBoundaryRawLoadOperator (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) : WhiteNoise →L[ℝ] HilbertVectorL2 (openCubeSet Q) :=
  (((ContinuousLinearMap.id ℝ ℝ).smulRight (HilbertVec.ofVec v)).compLpL 2
    (volume.restrict (openCubeSet Q))).comp
      (hilbertKernel (volume.restrict (openCubeSet Q))
        (q3SpatialKernel (openCubeSet Q) b L h3Zero))

/-- Its projected operator is the actual H10-gradient orthogonal projection. -/
def parentBoundaryDirichletLoadOperator (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) : WhiteNoise →L[ℝ] HilbertVectorL2 (openCubeSet Q) :=
  (lambda8H10GradientRange (isOpenBoundedConvexDomain_openCubeSet Q)).toSubmodule.starProjection.comp
    (parentBoundaryRawLoadOperator Q b L v)

/-- The raw operator has the literal same-noise physical source field. -/
theorem parent_boundary_raw_load_operator_coeFn (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) (w : WhiteNoise) :
    parentBoundaryRawLoadOperator Q b L v w =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => HilbertVec.ofVec (q3Convolution b L h3Zero w x • v) := by
  let C := (ContinuousLinearMap.id ℝ ℝ).smulRight (HilbertVec.ofVec v)
  let K := q3SpatialKernel (openCubeSet Q) b L h3Zero
  let T := hilbertKernel (volume.restrict (openCubeSet Q)) K
  filter_upwards [C.coeFn_compLp (T w),hilbertKernel_ae (volume.restrict (openCubeSet Q)) K w,
    (q3Section_memLp (openCubeSet Q) b L h3Zero).coeFn_toLp] with x hc ht hk
  change (parentBoundaryRawLoadOperator Q b L v w) x = C ((T w) x) at hc
  change K x=q3Section b L h3Zero x at hk
  rw [hc,ht,hk]
  rfl

/-- This operator agrees with the actual q3 raw basis-load class used by AN. -/
theorem parent_boundary_raw_load_basis (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) (n : whiteBasisIndex) :
    parentBoundaryRawLoadOperator Q b L v (whiteBasis n)=oldSignedRawVectorLoad Q b L n v := by
  apply Lp.ext
  exact (parent_boundary_raw_load_operator_coeFn Q b L v (whiteBasis n)).trans
    (old_signed_raw_vector_load_coeFn Q b L n v).symm

/-- On the original white basis the projection is precisely the gradient
of the selected actual parent potential, in the physical L2 carrier. -/
theorem parent_boundary_dirichlet_load_basis (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (v : Vec 2) (n : whiteBasisIndex) :
    parentBoundaryDirichletLoadOperator Q b L v (whiteBasis n)=
      (lambda8Q3GaussianModeParentPotential Q b L v n).toH1Function.gradToHilbertVectorL2 := by
  change lambda8DirichletProjection _
    (parentBoundaryRawLoadOperator Q b L v (whiteBasis n))=_
  rw [parent_boundary_raw_load_basis]
  exact (lambda8Q3GaussianModeParentPotential_spec Q b L v n).1

end
end ASDExplicitGamma.Native
