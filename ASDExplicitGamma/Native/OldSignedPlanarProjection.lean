module

public import ASDExplicitGamma.Native.OldSignedPhysicalH1
public import ASDExplicitGamma.Native.OldSignedProjectedTrace
public import ASDExplicitGamma.Variational.AdapterConstantSkew

/-! Planar whole-plane projection identities on the actual source squares.
The residual is a rotated genuine H1 gradient, so its divergence vanishes
without any assumed projection or derivative identity. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
open ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
noncomputable section

/-- Symmetry of the actual whole-plane projected white kernels. -/
theorem old_signed_projected_white_kernel_symmetric (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) :
    oldSignedProjectedWhiteKernel b L x i j=oldSignedProjectedWhiteKernel b L x j i := by
  apply congrArg oldSignedWhiteRealPart
  apply congrArg (oldSignedSpectralWhiteInverse b L)
  apply Lp.ext
  filter_upwards [old_signed_projected_character_coeFn b x i j,
    old_signed_projected_character_coeFn b x j i] with xi hij hji
  rw [hij,hji]
  simp only [oldSignedProjectedCharacterValue,oldSignedHelmholtzEntry,mul_comm]

/-- The actual whole-plane projected physical mode. -/
def oldSignedPhysicalProjectedField (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (j : Fin 2) (x : Vec 2) : Vec 2 :=
  fun i => inner ℝ w (oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) i j)

/-- Its pointwise trace is the original same physical q3 mode. -/
theorem old_signed_physical_projected_trace (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (x : Vec 2) :
    oldSignedPhysicalProjectedField b L w 0 x 0+oldSignedPhysicalProjectedField b L w 1 x 1=
      q3Convolution b L h3Zero w x := by
  change inner ℝ w (_:WhiteNoise)+inner ℝ w (_:WhiteNoise)=_
  rw [←inner_add_right,old_signed_projected_white_kernel_trace]
  simp only [smul_smul,mul_inv_cancel₀ L.2.ne',one_smul,q3Convolution]

/-- The projected physical vector is the actual gradient of its H1 potential. -/
theorem old_signed_physical_projected_grad (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (j : Fin 2) :
    (oldSignedProjectedModePotentialH1 Q b L w j).grad=oldSignedPhysicalProjectedField b L w j := by
  funext x i
  exact old_signed_projected_mode_potential_grad Q b L w j i x

/-- The complementary potential, with the signed quarter-turn input load. -/
def oldSignedComplementaryPotentialH1 (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (j : Fin 2) : H1Function (openCubeSet Q) :=
  (-responsePlanarJ 0 j) • oldSignedProjectedModePotentialH1 Q b L w 0+
    (-responsePlanarJ 1 j) • oldSignedProjectedModePotentialH1 Q b L w 1

/-- The whole-plane complement is exactly -J P J on the actual modes.
This preserves the source's quarter-turn signs and all boundary fluxes. -/
theorem old_signed_whole_plane_residual_rotated_gradient (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (j : Fin 2) :
    (fun x => q3Convolution b L h3Zero w x • basisVec j-oldSignedPhysicalProjectedField b L w j x)=
      fun x => matVecMul responsePlanarJ ((oldSignedComplementaryPotentialH1 Q b L w j).grad x) := by
  funext x i
  have ht := old_signed_physical_projected_trace b L w x
  have hs : oldSignedPhysicalProjectedField b L w 0 x 1=oldSignedPhysicalProjectedField b L w 1 x 0 :=
    congrArg (inner ℝ w) (old_signed_projected_white_kernel_symmetric b L (L.1⁻¹ • x) 1 0)
  simp only [oldSignedComplementaryPotentialH1,H1Function.add_grad,H1Function.smul_grad,
    old_signed_physical_projected_grad]
  fin_cases j <;> fin_cases i <;>
    norm_num [matVecMul,responsePlanarJ,basisVec_apply,Fin.sum_univ_two] <;> linarith only [ht,hs]

/-- The actual whole-plane complement is solenoidal on every source square;
its H1 potential has been constructed rather than assumed. -/
theorem old_signed_whole_plane_residual_solenoidal (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (j : Fin 2) :
    IsSolenoidalOn (openCubeSet Q)
      (fun x => q3Convolution b L h3Zero w x • basisVec j-oldSignedPhysicalProjectedField b L w j x) := by
  rw [old_signed_whole_plane_residual_rotated_gradient Q b L w j]
  apply constant_skew_gradient_isSolenoidal
  ext i k
  fin_cases i <;> fin_cases k <;> norm_num [matTranspose,responsePlanarJ]

end
end ASDExplicitGamma.Native
