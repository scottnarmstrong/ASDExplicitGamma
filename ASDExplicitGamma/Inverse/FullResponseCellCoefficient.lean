module

public import ASDExplicitGamma.Inverse.ResponseCoefficients

/-! Exact conversion of the physical open-cell response representative to the
closed cube used by the trace-defect API. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory ASDExplicitGamma.Response

/-- Restrict the chosen global representative of an open-cell response
coefficient to the exact closed physical cube. -/
noncomputable def responseCoefficientOnClosedCube (Q : TriadicCube 2)
    (k : ResponseCoefficient (openCubeSet Q)) : ResponseCoefficient (cubeSet Q) :=
  (responseCoefficientExtension k).compContinuous
    ⟨Subtype.val, continuous_subtype_val⟩

/-- The closed-cube coefficient retains the same global response field at
every point of the physical cube, including its boundary. -/
theorem responseCoefficientOnClosedCube_extension_eq (Q : TriadicCube 2)
    (k : ResponseCoefficient (openCubeSet Q)) {x : Vec 2} (hx : x ∈ cubeSet Q) :
    responseCoefficientExtension (responseCoefficientOnClosedCube Q k) x =
      responseCoefficientExtension k x := by
  rw [responseCoefficientExtension_eq (responseCoefficientOnClosedCube Q k) hx]
  simp [responseCoefficientOnClosedCube, BoundedContinuousFunction.compContinuous_apply]

end ASDExplicitGamma.Inverse
