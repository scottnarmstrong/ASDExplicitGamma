module

public import ASDExplicitGamma.Native.OldSignedFlatDirichletEnergy
public import ASDExplicitGamma.Native.OldSignedFlatAdmissibility

/-! Actual doubled flat trial inputs, with the source signs and parent
boundary conditions. The plus and minus inputs have disjoint load blocks. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
noncomputable section

/-- The actual plus input on a top load is (0,-G(psi J e_i)). -/
def oldSignedFlatPlusBlock (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) (x : Vec 2) : BlockVec 2 :=
  (0,fun k => -mainFlatPlusCoordinate Q b L n (i,k) x)

/-- The actual minus input on a bottom load is (P_D(psi J e_i),0). -/
def oldSignedFlatMinusBlock (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (i : Fin 2) (x : Vec 2) : BlockVec 2 :=
  (fun k => mainFlatMinusCoordinate Q b L n (i,k) x,0)

/-- The source plus input is genuinely L2. -/
theorem old_signed_flat_plus_block_memL2 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    MemBlockL2 (openCubeSet Q) (oldSignedFlatPlusBlock Q b L n i) :=
  memBlockL2_blockField MemLp.zero (old_signed_flat_plus_memL2 Q b L n i).neg

/-- The source minus input is genuinely L2. -/
theorem old_signed_flat_minus_block_memL2 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    MemBlockL2 (openCubeSet Q) (oldSignedFlatMinusBlock Q b L n i) :=
  memBlockL2_blockField (old_signed_flat_minus_memL2 Q b L n i) MemLp.zero

/-- The actual minus flat input is an admissible parent variation. -/
theorem old_signed_flat_minus_block_variation (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    ScalarVariation (openCubeSet Q) (oldSignedFlatMinusBlock Q b L n i) :=
  ⟨old_signed_flat_minus_block_memL2 Q b L n i,
    old_signed_flat_minus_potential_zero_trace Q b L n i,isSolenoidalZeroNormalTraceOn_zero⟩

/-- The plus flat input minus the physical shear of the top affine load
is an actual parent variation, including the zero-normal boundary trace. -/
theorem old_signed_flat_plus_affine_difference_variation (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    ScalarVariation (openCubeSet Q) (fun x => oldSignedFlatPlusBlock Q b L n i x-
      (0,-(q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i))) := by
  have hr : MemVectorL2 (openCubeSet Q) (fun x =>
      q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i) := by
    exact old_signed_rotated_raw_load_memL2 Q b L (whiteBasis n) i
  refine ⟨(old_signed_flat_plus_block_memL2 Q b L n i).sub
    (memBlockL2_blockField MemLp.zero hr.neg),?_,?_⟩
  · change IsPotentialZeroTraceOn (openCubeSet Q) (fun _ => (0:Vec 2)-(0:Vec 2))
    refine ⟨0,?_⟩
    funext x j
    change (0:ℝ)=0-0
    ring
  · have hsol := isSolenoidalZeroNormalTraceOn_smul
      (old_signed_flat_plus_removed_zero_normal Q b L n i) (-1)
    convert hsol using 1
    funext x k
    simp only [oldSignedFlatPlusBlock,Prod.snd_sub,Pi.smul_apply,smul_eq_mul,
      Pi.sub_apply,Pi.neg_apply]
    ring

end
end ASDExplicitGamma.Native
