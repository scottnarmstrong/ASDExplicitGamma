module

public import ASDExplicitGamma.Native.OldSignedFlatBlockFields
public import ASDExplicitGamma.Native.OldSignedShearGauge

/-! The literal physical nilpotent shear on doubled field representatives,
for the local signed trial's parent membership calculation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Main ASDExplicitGamma.Gaussian
noncomputable section

/-- The physical skew shear as a real-linear map on doubled fields. -/
def oldSignedPointwiseShear (eta : Vec 2 → ℝ) :
    (Vec 2 → BlockVec 2) →ₗ[ℝ] (Vec 2 → BlockVec 2) where
  toFun X x := (0,-(eta x • matVecMul responsePlanarJ (X x).1))
  map_add' X Y := by
    funext x
    apply Prod.ext
    · simp
    · change -(eta x • matVecMul responsePlanarJ ((X x).1+(Y x).1))=
        -(eta x • matVecMul responsePlanarJ (X x).1)+
          -(eta x • matVecMul responsePlanarJ (Y x).1)
      rw [matVecMul_add,smul_add]
      abel
  map_smul' c X := by
    funext x
    apply Prod.ext
    · simp
    · change -(eta x • matVecMul responsePlanarJ (c • (X x).1))=
        c • (-(eta x • matVecMul responsePlanarJ (X x).1))
      simp only [matVecMul_smul,smul_neg,smul_smul]
      rw [mul_comm (eta x) c]

/-- The actual plus flat input minus the physical top-affine shear is an
admissible parent variation, in the same linear-map convention as the trial. -/
theorem old_signed_flat_plus_pointwise_shear_variation (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    Scalar.ScalarVariation (openCubeSet Q) (oldSignedFlatPlusBlock Q b L n i-
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        (fun _ => (basisVec i,0))) := by
  convert old_signed_flat_plus_affine_difference_variation Q b L n i using 1
  funext x
  rfl

end
end ASDExplicitGamma.Native
