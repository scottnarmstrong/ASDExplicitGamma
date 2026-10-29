module

public import ASDExplicitGamma.Native.OldSignedFlatMembership

/-! Physical whole-plane projections of the source rotated affine loads,
with honest H1 potentials and the same unprojected divergence. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
noncomputable section

/-- The actual whole-plane projection of psi J e_i, by rotating its input
load only. Its covariance contraction includes the other J separately. -/
def oldSignedRotatedProjectedField (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (i : Fin 2) : Vec 2 → Vec 2 :=
  fun x => responsePlanarJ 0 i • oldSignedPhysicalProjectedField b L w 0 x+
    responsePlanarJ 1 i • oldSignedPhysicalProjectedField b L w 1 x

/-- A genuine physical H1 potential of the rotated-input whole-plane mode. -/
def oldSignedRotatedProjectedPotentialH1 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (i : Fin 2) : H1Function (openCubeSet Q) :=
  responsePlanarJ 0 i • oldSignedProjectedModePotentialH1 Q b L w 0+
    responsePlanarJ 1 i • oldSignedProjectedModePotentialH1 Q b L w 1

/-- The constructed potential has exactly the required physical gradient. -/
theorem old_signed_rotated_projected_grad (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (i : Fin 2) :
    (oldSignedRotatedProjectedPotentialH1 Q b L w i).grad=oldSignedRotatedProjectedField b L w i := by
  simp only [oldSignedRotatedProjectedPotentialH1,H1Function.add_grad,H1Function.smul_grad,
    old_signed_physical_projected_grad]
  rfl

/-- The actual rotated projected fields are locally square integrable. -/
theorem old_signed_rotated_projected_memL2 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (i : Fin 2) :
    MemVectorL2 (openCubeSet Q) (oldSignedRotatedProjectedField b L w i) := by
  rw [←old_signed_rotated_projected_grad Q b L w i]
  exact (oldSignedRotatedProjectedPotentialH1 Q b L w i).grad_memVectorL2

/-- The actual rotated whole-plane projection has the original load's
divergence on every square, with no equality of projectors assumed. -/
theorem old_signed_rotated_projected_residual_solenoidal (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (i : Fin 2) :
    IsSolenoidalOn (openCubeSet Q) (fun x =>
      q3Convolution b L h3Zero w x • mainFlatRotatedBasis i-
        oldSignedRotatedProjectedField b L w i x) := by
  fin_cases i
  · have hb : mainFlatRotatedBasis 0=basisVec 1 := by
      ext k
      fin_cases k <;> norm_num [mainFlatRotatedBasis,matVecMul,responsePlanarJ,basisVec,Fin.sum_univ_two,Pi.single_apply]
    simpa [hb,oldSignedRotatedProjectedField,responsePlanarJ] using
      old_signed_whole_plane_residual_solenoidal Q b L w 1
  · have h := isSolenoidalOn_smul (old_signed_whole_plane_residual_solenoidal Q b L w 0) (-1)
    convert h using 1
    funext x k
    fin_cases k <;> simp [oldSignedRotatedProjectedField,mainFlatRotatedBasis,responsePlanarJ,
      matVecMul,basisVec,Fin.sum_univ_two,sub_eq_add_neg,add_comm]

end
end ASDExplicitGamma.Native
