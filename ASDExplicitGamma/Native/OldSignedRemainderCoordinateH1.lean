module

public import ASDExplicitGamma.Native.OldSignedProjectedGradientTrace
public import ASDExplicitGamma.Native.OldSignedPlusRemainderEnergy

/-! Actual H1 coordinate witnesses for both harmonic boundary remainders.
The whole-plane complementary mode is the output rotation of the projected
unrotated mode, preserving its exact derivative trace. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response
noncomputable section

/-- In the plane, (I-P_infinity)J=J P_infinity on the actual physical
q3 modes. The identity uses the proved full trace and matrix symmetry. -/
theorem old_signed_complementary_output_rotation (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (i : Fin 2) :
    oldSignedRotatedComplementaryField b L w i=fun x =>
      matVecMul responsePlanarJ (oldSignedPhysicalProjectedField b L w i x) := by
  funext x k
  have ht := old_signed_physical_projected_trace b L w x
  have hs := congrArg (inner ℝ w) (old_signed_projected_white_kernel_symmetric b L (L.1⁻¹ • x) 0 1)
  change oldSignedPhysicalProjectedField b L w 1 x 0=oldSignedPhysicalProjectedField b L w 0 x 1 at hs
  fin_cases i <;> fin_cases k
  all_goals norm_num [oldSignedRotatedComplementaryField,oldSignedRotatedProjectedField,
    old_signed_rotated_basis_zero,old_signed_rotated_basis_one,matVecMul,responsePlanarJ,
    basisVec,Pi.single_apply,Fin.sum_univ_two]
  all_goals linarith only [ht,hs]

/-- Input-rotated projected mode, as an actual H1 coordinate. -/
def oldSignedRotatedProjectedCoordinateH1 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (a : Fin 2 × Fin 2) : H1Function (openCubeSet Q) :=
  responsePlanarJ 0 a.1 • oldSignedProjectedPhysicalCoordinateH1 Q b L w a.2 0+
    responsePlanarJ 1 a.1 • oldSignedProjectedPhysicalCoordinateH1 Q b L w a.2 1

/-- The complementary source mode, represented as an output-rotated H1
coordinate of the actual projected unrotated mode. -/
def oldSignedComplementaryCoordinateH1 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (a : Fin 2 × Fin 2) : H1Function (openCubeSet Q) :=
  responsePlanarJ a.2 0 • oldSignedProjectedPhysicalCoordinateH1 Q b L w 0 a.1+
    responsePlanarJ a.2 1 • oldSignedProjectedPhysicalCoordinateH1 Q b L w 1 a.1

/-- The H1 input rotation is the literal physical projected rotated field. -/
theorem old_signed_rotated_projected_coordinate_toFun (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (i k : Fin 2) (x : Vec 2) :
    oldSignedRotatedProjectedCoordinateH1 Q b L w (i,k) x=oldSignedRotatedProjectedField b L w i x k := by
  simp only [oldSignedRotatedProjectedCoordinateH1,H1Function.add_toFun,H1Function.smul_toFun]
  rfl

/-- The H1 output rotation is the literal physical complementary source. -/
theorem old_signed_complementary_coordinate_toFun (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (i k : Fin 2) (x : Vec 2) :
    oldSignedComplementaryCoordinateH1 Q b L w (i,k) x=oldSignedRotatedComplementaryField b L w i x k := by
  rw [old_signed_complementary_output_rotation]
  simp only [oldSignedComplementaryCoordinateH1,H1Function.add_toFun,H1Function.smul_toFun]
  change _=(∑ j : Fin 2,responsePlanarJ k j*oldSignedPhysicalProjectedField b L w i x j)
  rw [Fin.sum_univ_two]
  rfl

/-- Actual H1 positive remainder, using complementary-minus-removed fields
so both derivative energy terms have the sharp sigma² trace. -/
def oldSignedFlatPlusRemainderCoordinateH1 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (a : Fin 2 × Fin 2) : H1Function (openCubeSet Q) :=
  oldSignedComplementaryCoordinateH1 Q b L (whiteBasis n) a-mainFlatPlusCorrectionCoordinate Q b L n a

/-- Actual H1 negative remainder, with its unchanged Dirichlet boundary. -/
def oldSignedFlatMinusRemainderCoordinateH1 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (a : Fin 2 × Fin 2) : H1Function (openCubeSet Q) :=
  mainFlatMinusCoordinate Q b L n a-oldSignedRotatedProjectedCoordinateH1 Q b L (whiteBasis n) a

/-- Both coordinate witnesses have the actual source remainder as value. -/
theorem old_signed_flat_plus_remainder_coordinate_toFun (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i k : Fin 2) (x : Vec 2) :
    oldSignedFlatPlusRemainderCoordinateH1 Q b L n (i,k) x=oldSignedFlatPlusRemainder Q b L n i x k := by
  simp only [oldSignedFlatPlusRemainderCoordinateH1,H1Function.sub_toFun]
  rw [old_signed_complementary_coordinate_toFun,old_signed_flat_plus_correction]
  simp only [oldSignedRotatedComplementaryField,oldSignedFlatPlusRemainder,Pi.sub_apply]
  rw [old_signed_flat_plus_coordinate]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

theorem old_signed_flat_minus_remainder_coordinate_toFun (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i k : Fin 2) (x : Vec 2) :
    oldSignedFlatMinusRemainderCoordinateH1 Q b L n (i,k) x=oldSignedFlatMinusRemainder Q b L n i x k := by
  simp only [oldSignedFlatMinusRemainderCoordinateH1,H1Function.sub_toFun]
  rw [old_signed_rotated_projected_coordinate_toFun]
  rfl

end
end ASDExplicitGamma.Native
