module

public import ASDExplicitGamma.Native.OldSignedProjectedDerivativeCovariance

/-! Actual H1 coordinate fields of the physical whole-plane projected modes,
with their exact length-scaled first derivatives. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
noncomputable section

/-- Each physical projected scalar coordinate is globally C1. -/
theorem old_signed_projected_physical_coordinate_contDiff (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (i j : Fin 2) :
    ContDiff ℝ 1 (fun x => oldSignedPhysicalProjectedField b L w j x i) := by
  have hs : ContDiff ℝ 1 (fun x : Vec 2 => L.1⁻¹ • x) :=
    (L.1⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)).contDiff
  exact (innerSL ℝ w).contDiff.comp ((oldSignedPotentialWhiteMap b L).contDiff.comp
    ((old_signed_projected_character_contDiff b i j).comp hs))

/-- The actual physical coordinate as an H1 function on the source square. -/
def oldSignedProjectedPhysicalCoordinateH1 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (i j : Fin 2) : H1Function (openCubeSet Q) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
    (old_signed_projected_physical_coordinate_contDiff b L w i j)

/-- The physical coordinate has the strong derivative transported through
the actual white map and inverse shell-length scaling. -/
theorem old_signed_projected_physical_coordinate_hasFDerivAt (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (x : Vec 2) (i j : Fin 2) :
    HasFDerivAt (fun y => oldSignedPhysicalProjectedField b L w j y i)
      ((innerSL ℝ w).comp (((oldSignedPotentialWhiteMap b L).comp
        (oldSignedProjectedSpatialDerivative b (L.1⁻¹ • x) i j)).comp
          (L.1⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)))) x :=
  (innerSL ℝ w).hasFDerivAt.comp x
    ((old_signed_projected_white_hasFDerivAt b L (L.1⁻¹ • x) i j).comp x
      ((L.1⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt))

/-- No physical shell-length factor is lost in the actual H1 gradient. -/
theorem old_signed_projected_physical_coordinate_grad (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (i j k : Fin 2) (x : Vec 2) :
    (oldSignedProjectedPhysicalCoordinateH1 Q b L w i j).grad x k=
      L.1⁻¹*inner ℝ w (oldSignedProjectedDerivativeWhiteKernel b L (L.1⁻¹ • x) i j k) := by
  change (fderiv ℝ (fun y => oldSignedPhysicalProjectedField b L w j y i) x) (basisVec k)=_
  rw [(old_signed_projected_physical_coordinate_hasFDerivAt b L w x i j).fderiv]
  change inner ℝ w (((oldSignedPotentialWhiteMap b L).comp
    (oldSignedProjectedSpatialDerivative b (L.1⁻¹ • x) i j))
      ((L.1⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)) (basisVec k)))=_
  rw [smul_apply,ContinuousLinearMap.id_apply,map_smul,old_signed_projected_white_derivative_basis,
    real_inner_smul_right]

end
end ASDExplicitGamma.Native
