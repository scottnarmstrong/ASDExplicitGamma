module

public import ASDExplicitGamma.Native.OldSignedPointwiseShear
public import ASDExplicitGamma.Response.ResponseRealization

/-! Actual physical response directions for the normalized OLD shear.
The factor sigma is retained in the coefficient direction; dividing by
sigma in the response operator recovers exactly the OLD multiplier. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Gaussian
noncomputable section

/-- The physical direction sigma psi on the closed observation square. -/
def oldSignedPhysicalCoefficient (Q : TriadicCube 2) (sigma b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) : ResponseCoefficient (openCubeSet Q) := by
  letI oldSignedDirectionCompact : CompactSpace (closure (openCubeSet Q)) :=
    isCompact_iff_compactSpace.mp (isBounded_openCubeSet Q).isCompact_closure
  exact BoundedContinuousFunction.mkOfCompact
    ⟨fun x => sigma * q3Convolution b L h3Zero (whiteBasis n) x.1,
      continuous_const.mul ((q3Convolution_continuous b L h3Zero
        (whiteBasis n)).comp continuous_subtype_val)⟩

/-- On the actual square the normalized physical multiplier is psi. -/
theorem old_signed_physical_coefficient_value (Q : TriadicCube 2) (sigma b : ℝ)
    (hsigma : 0 < sigma) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    {x : Vec 2} (hx : x ∈ openCubeSet Q) :
    responseCoefficientExtension (oldSignedPhysicalCoefficient Q sigma b L n) x / sigma =
      q3Convolution b L h3Zero (whiteBasis n) x := by
  rw [responseCoefficientExtension_eq _ hx]
  change (sigma * _) / sigma = _
  exact mul_div_cancel_left₀ _ hsigma.ne'

/-- The genuine L2 response shear has exactly the plain physical action
used in the local trial membership calculation. -/
theorem old_signed_physical_shear_representative (Q : TriadicCube 2) (sigma b : ℝ)
    (hsigma : 0 < sigma) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex)
    (X : HilbertBlockL2 (openCubeSet Q)) :
    hilbertBlockL2ToBlockL2 (responseShearL2Operator sigma hsigma
      (oldSignedPhysicalCoefficient Q sigma b L n) X) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (hilbertBlockL2ToBlockL2 X) := by
  filter_upwards [responseShearL2Operator_toBlockL2_ae sigma hsigma
    (oldSignedPhysicalCoefficient Q sigma b L n) X,
    ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx hmem
  rw [hx]
  change (0,-((responseCoefficientExtension (oldSignedPhysicalCoefficient Q sigma b L n) x / sigma) •
    matVecMul responsePlanarJ (hilbertBlockL2ToBlockL2 X x).1)) =
      (0,-(q3Convolution b L h3Zero (whiteBasis n) x •
        matVecMul responsePlanarJ (hilbertBlockL2ToBlockL2 X x).1))
  rw [old_signed_physical_coefficient_value Q sigma b hsigma L n hmem]


end
end ASDExplicitGamma.Native
