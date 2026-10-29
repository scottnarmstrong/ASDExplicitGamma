module

public import ASDExplicitGamma.Native.OldSignedRotatedProjectedField

/-! The physical flat-mode differences in AN (2.3) are genuine harmonic
gradients, with all boundary projections on the same parent square. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
noncomputable section

/-- Subtraction preserves distributional solenoidality for genuine L2
fields; all integral linearity hypotheses are supplied from L2. -/
theorem old_signed_solenoidal_sub {d : ℕ} {U : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : MemVectorL2 U F) (hG : MemVectorL2 U G)
    (hsF : IsSolenoidalOn U F) (hsG : IsSolenoidalOn U G) :
    IsSolenoidalOn U (fun x => F x-G x) := by
  intro φ
  have he : (fun x => vecDot (F x-G x) (φ.toH1Function.grad x))=
      (fun x => vecDot (F x) (φ.toH1Function.grad x))-
        (fun x => vecDot (G x) (φ.toH1Function.grad x)) := by
    funext x
    simp [vecDot,Finset.sum_sub_distrib,sub_mul]
  rw [he]
  change (∫ x in U,vecDot (F x) (φ.toH1Function.grad x)-vecDot (G x) (φ.toH1Function.grad x) ∂volume)=0
  rw [integral_sub (integrableOn_vecDot_of_memVectorL2 hF φ.toH1Function.grad_memVectorL2)
    (integrableOn_vecDot_of_memVectorL2 hG φ.toH1Function.grad_memVectorL2),hsF φ,hsG φ,sub_self]

/-- The source positive remainder, as an actual physical field. -/
def oldSignedFlatPlusRemainder (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) : Vec 2 → Vec 2 :=
  fun x => (fun k => mainFlatPlusCoordinate Q b L n (i,k) x)-
    oldSignedRotatedProjectedField b L (whiteBasis n) i x

/-- The source negative remainder, as an actual physical field. -/
def oldSignedFlatMinusRemainder (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) : Vec 2 → Vec 2 :=
  fun x => (fun k => mainFlatMinusCoordinate Q b L n (i,k) x)-
    oldSignedRotatedProjectedField b L (whiteBasis n) i x

/-- Both actual boundary remainders are square integrable. -/
theorem old_signed_flat_remainders_memL2 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    MemVectorL2 (openCubeSet Q) (oldSignedFlatPlusRemainder Q b L n i) ∧
      MemVectorL2 (openCubeSet Q) (oldSignedFlatMinusRemainder Q b L n i) :=
  ⟨(old_signed_flat_plus_memL2 Q b L n i).sub (old_signed_rotated_projected_memL2 Q b L (whiteBasis n) i),
    (old_signed_flat_minus_memL2 Q b L n i).sub (old_signed_rotated_projected_memL2 Q b L (whiteBasis n) i)⟩

/-- The positive boundary remainder is an actual H1 gradient. -/
theorem old_signed_flat_plus_remainder_potential (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    IsPotentialOn (openCubeSet Q) (oldSignedFlatPlusRemainder Q b L n i) := by
  obtain ⟨u,hu⟩ := old_signed_flat_plus_potential Q b L n i
  refine ⟨u-oldSignedRotatedProjectedPotentialH1 Q b L (whiteBasis n) i,?_⟩
  rw [H1Function.sub_grad,hu,old_signed_rotated_projected_grad]
  rfl

/-- The negative remainder is harmonic: its distributional divergence
vanishes by the two actual projection residual identities. -/
theorem old_signed_flat_minus_remainder_solenoidal (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    IsSolenoidalOn (openCubeSet Q) (oldSignedFlatMinusRemainder Q b L n i) := by
  let F := fun x => q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i
  have hF : MemVectorL2 (openCubeSet Q) F :=
    lambda8H1ComponentField_memVectorL2
      (fun k => lambda8Q3GaussianModeLoadH1 Q b L (mainFlatRotatedBasis i) n k)
  have hD := old_signed_q3_parent_residual_solenoidal Q b L (mainFlatRotatedBasis i) n
  have hP := old_signed_rotated_projected_residual_solenoidal Q b L (whiteBasis n) i
  have hh := old_signed_solenoidal_sub
    (hF.sub (old_signed_rotated_projected_memL2 Q b L (whiteBasis n) i))
    (hF.sub (lambda8Q3GaussianModeParentPotential Q b L (mainFlatRotatedBasis i) n).toH1Function.grad_memVectorL2)
    hP hD
  convert hh using 1
  funext x k
  rw [oldSignedFlatMinusRemainder,Pi.sub_apply,old_signed_flat_minus_coordinate]
  simp only [Pi.sub_apply]
  ring

/-- The positive remainder is harmonic: its divergence vanishes because
the finite all-gradient and the whole-plane projections preserve the same
original divergence. The finite projection correction keeps zero normal trace. -/
theorem old_signed_flat_plus_remainder_solenoidal (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    IsSolenoidalOn (openCubeSet Q) (oldSignedFlatPlusRemainder Q b L n i) := by
  let F := fun x => q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i
  let G := fun x k => mainFlatPlusCoordinate Q b L n (i,k) x
  let P := oldSignedRotatedProjectedField b L (whiteBasis n) i
  have hF : MemVectorL2 (openCubeSet Q) F :=
    lambda8H1ComponentField_memVectorL2
      (fun k => lambda8Q3GaussianModeLoadH1 Q b L (mainFlatRotatedBasis i) n k)
  have hP : MemVectorL2 (openCubeSet Q) P := old_signed_rotated_projected_memL2 Q b L (whiteBasis n) i
  have hG : MemVectorL2 (openCubeSet Q) G := old_signed_flat_plus_memL2 Q b L n i
  have hres : IsSolenoidalOn (openCubeSet Q) (fun x => G x-F x) :=
    fun φ => old_signed_flat_plus_removed_zero_normal Q b L n i φ.toH1Function
  have hh := isSolenoidalOn_add
    (old_signed_rotated_projected_residual_solenoidal Q b L (whiteBasis n) i) hres
    (fun φ => integrableOn_vecDot_of_memVectorL2 (hF.sub hP) φ.toH1Function.grad_memVectorL2)
    (fun φ => integrableOn_vecDot_of_memVectorL2 (hG.sub hF) φ.toH1Function.grad_memVectorL2)
  convert hh using 1
  funext x k
  change G x k-P x k=(F x k-P x k)+(G x k-F x k)
  ring

end
end ASDExplicitGamma.Native
