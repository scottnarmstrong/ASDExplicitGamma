module

public import ASDExplicitGamma.Native.OldSignedComplementaryEnergyTrace
public import ASDExplicitGamma.Native.OldSignedRotatedProjectedField
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! The complementary kernels are exactly the physical residuals of the
actual projected q3 fields, with the original source input orientation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Main ASDExplicitGamma.Response ASDExplicitGamma.Triadic
noncomputable section

/-- Actual physical residual of the whole-plane projected rotated load. -/
def oldSignedRotatedComplementaryField (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (i : Fin 2) : Vec 2 → Vec 2 :=
  fun x => q3Convolution b L h3Zero w x • mainFlatRotatedBasis i-
    oldSignedRotatedProjectedField b L w i x

/-- An actual complementary white-mode coefficient equals the physical
unprojected load minus its full whole-plane projection. -/
theorem old_signed_complementary_white_mode (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (x : Vec 2) (i j : Fin 2) :
    inner ℝ w (oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) i j)=
      (if i=j then q3Convolution b L h3Zero w x else 0)-
        oldSignedPhysicalProjectedField b L w j x i := by
  have hx : L.1 • (L.1⁻¹ • x)=x := by
    rw [smul_smul,mul_inv_cancel₀ L.2.ne',one_smul]
  rw [oldSignedComplementaryWhiteKernel,inner_sub_right,hx]
  split_ifs <;> simp only [inner_zero_right,oldSignedPhysicalProjectedField,q3Convolution]

/-- Source quarter turn of the first coordinate load. -/
theorem old_signed_rotated_basis_zero : mainFlatRotatedBasis 0=basisVec 1 := by
  ext k
  fin_cases k <;> norm_num [mainFlatRotatedBasis,matVecMul,responsePlanarJ,basisVec,Fin.sum_univ_two,Pi.single_apply]

/-- Source quarter turn of the second coordinate load, retaining its sign. -/
theorem old_signed_rotated_basis_one : mainFlatRotatedBasis 1= -basisVec 0 := by
  ext k
  fin_cases k <;> norm_num [mainFlatRotatedBasis,matVecMul,responsePlanarJ,basisVec,Fin.sum_univ_two,Pi.single_apply]

/-- The complementary physical family is the same signed permutation of
the actual complementary white kernels as the projected physical family. -/
theorem old_signed_rotated_complementary_energy_sum (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    (∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x => oldSignedRotatedComplementaryField b L (whiteBasis n) i x k))=
      ∑ i : Fin 2,∑ j : Fin 2,energy Q (fun x =>
        inner ℝ (whiteBasis n) (oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) i j)) := by
  have h0 (k : Fin 2) : (fun x => oldSignedRotatedComplementaryField b L (whiteBasis n) 0 x k)=
      fun x => inner ℝ (whiteBasis n) (oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) k 1) := by
    funext x
    rw [old_signed_complementary_white_mode]
    simp [oldSignedRotatedComplementaryField,oldSignedRotatedProjectedField,
      old_signed_rotated_basis_zero,responsePlanarJ,basisVec,Pi.single_apply,oldSignedPhysicalProjectedField]
  have h1 (k : Fin 2) : (fun x => oldSignedRotatedComplementaryField b L (whiteBasis n) 1 x k)=
      fun x => -inner ℝ (whiteBasis n) (oldSignedComplementaryWhiteKernel b L (L.1⁻¹ • x) k 0) := by
    funext x
    rw [old_signed_complementary_white_mode]
    simp [oldSignedRotatedComplementaryField,oldSignedRotatedProjectedField,
      old_signed_rotated_basis_one,responsePlanarJ,basisVec,Pi.single_apply,oldSignedPhysicalProjectedField,sub_eq_add_neg,add_comm]
  simp only [Fin.sum_univ_two,h0,h1,energy_neg]
  ring

/-- The whole-plane complementary family also has exactly one shell
variance of complete normalized spatial energy. -/
theorem old_signed_rotated_complementary_energy_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    HasSum (fun n : whiteBasisIndex => ∑ i : Fin 2,∑ k : Fin 2,energy Q
      (fun x => oldSignedRotatedComplementaryField b L (whiteBasis n) i x k)) (b^2) :=
  (old_signed_complementary_total_spatial_energy_trace Q b L).congr_fun
    (fun n => old_signed_rotated_complementary_energy_sum Q b L n)

end
end ASDExplicitGamma.Native
