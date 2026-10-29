module

public import ASDExplicitGamma.Native.OldSignedRemainderCovarianceVector
public import ASDExplicitGamma.Native.OldSignedPhysicalCovarianceIntegral

/-! Literal decomposition of the actual finite-square flat fields into
whole-plane projected modes and the actual harmonic remainder modes. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
open ASDExplicitGamma.Response
noncomputable section

/-- Select the actual plus or minus flat field, with unchanged load signs. -/
def oldSignedFlatCoordinate (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (plus : Bool) : whiteBasisIndex → Fin 2 × Fin 2 → H1Function (openCubeSet Q) :=
  if plus then mainFlatPlusCoordinate Q b L else mainFlatMinusCoordinate Q b L

/-- Both actual flat modes split into the same whole-plane projection and
their corresponding actual harmonic remainders. -/
theorem old_signed_flat_coordinate_decomposition (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (n : whiteBasisIndex) (i k : Fin 2) (x : Vec 2) :
    oldSignedFlatCoordinate Q b L plus n (i,k) x=
      oldSignedRotatedProjectedField b L (whiteBasis n) i x k+
        oldSignedRemainderCoordinate Q b L plus n (i,k) x := by
  cases plus
  · simp only [oldSignedFlatCoordinate,oldSignedRemainderCoordinate,Bool.false_eq_true,↓reduceIte]
    rw [old_signed_flat_minus_remainder_coordinate_toFun]
    simp only [oldSignedFlatMinusRemainder,Pi.sub_apply]
    ring
  · simp only [oldSignedFlatCoordinate,oldSignedRemainderCoordinate,↓reduceIte]
    rw [old_signed_flat_plus_remainder_coordinate_toFun]
    simp only [oldSignedFlatPlusRemainder,Pi.sub_apply]
    ring

/-- The output rotation of the actual projected physical mode is exactly
the signed J P_infinity J white kernel, including both rotations. -/
theorem old_signed_rotated_projected_output_kernel (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (i k : Fin 2) (x : Vec 2) :
    matVecMul responsePlanarJ (oldSignedRotatedProjectedField b L w i x) k=
      inner ℝ w (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) k i) := by
  simp only [oldSignedRotatedWhiteKernel,Fin.sum_univ_two,inner_add_right,real_inner_smul_right,
    oldSignedRotatedProjectedField,oldSignedPhysicalProjectedField,matVecMul,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

/-- Exact signed mode decomposition after the source output rotation. -/
theorem old_signed_flat_output_decomposition (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (n : whiteBasisIndex) (i k : Fin 2) (x : Vec 2) :
    matVecMul responsePlanarJ (fun l => oldSignedFlatCoordinate Q b L plus n (i,l) x) k=
      inner ℝ (whiteBasis n) (oldSignedRotatedWhiteKernel b L (L.1⁻¹ • x) k i)+
        matVecMul responsePlanarJ (fun l => oldSignedRemainderCoordinate Q b L plus n (i,l) x) k := by
  simp_rw [old_signed_flat_coordinate_decomposition]
  rw [matVecMul]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  exact old_signed_rotated_projected_output_kernel b L (whiteBasis n) i k x

end
end ASDExplicitGamma.Native
