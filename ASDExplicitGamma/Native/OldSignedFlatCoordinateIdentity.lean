module

public import ASDExplicitGamma.Native.OldSignedHodgeFields
public import ASDExplicitGamma.Main.FlatFieldH1Bounds

/-! The existing flat H1 coordinates are the literal physical OLD fields,
with the source quarter-turn orientation and actual Dirichlet potential. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Triadic
noncomputable section

/-- The existing minus coordinates are the actual parent Dirichlet gradient. -/
theorem old_signed_flat_minus_coordinate (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i k : Fin 2) (x : Vec 2) :
    mainFlatMinusCoordinate Q b L n (i,k) x=
      (lambda8Q3GaussianModeParentPotential Q b L (mainFlatRotatedBasis i) n).toH1Function.grad x k := by
  change inner ℝ (HilbertVec.ofVec (basisVec k))
    (HilbertVec.ofVec ((lambda8Q3GaussianModeParentPotential Q b L
      (mainFlatRotatedBasis i) n).toH1Function.grad x))=_
  rw [HilbertVec.inner_def,vecDot_basisVec_left]

/-- The correction in the existing plus coordinates is the signed physical
rotation of the same parent Dirichlet gradient. -/
theorem old_signed_flat_plus_correction (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i k : Fin 2) (x : Vec 2) :
    mainFlatPlusCorrectionCoordinate Q b L n (i,k) x=
      matVecMul responsePlanarJ
        ((lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad x) k := by
  change inner ℝ (HilbertVec.ofVec (basisVec k))
    (HilbertVec.ofVec (matVecMul responsePlanarJ
      ((lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad x)))=_
  rw [HilbertVec.inner_def,vecDot_basisVec_left]

/-- The plus field is exactly psi J e_i-J P_D(psi e_i), with no choice of
source gauge or different boundary potential. -/
theorem old_signed_flat_plus_coordinate (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i k : Fin 2) (x : Vec 2) :
    mainFlatPlusCoordinate Q b L n (i,k) x=
      q3Convolution b L h3Zero (whiteBasis n) x*mainFlatRotatedBasis i k-
        matVecMul responsePlanarJ
          ((lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad x) k := by
  simp only [mainFlatPlusCoordinate,H1Function.sub_toFun]
  rw [old_signed_flat_plus_correction]
  rfl

/-- The actual minus flat field belongs to the literal zero-trace
potential space, before any weighted local lifting. -/
theorem old_signed_flat_minus_potential_zero_trace (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    IsPotentialZeroTraceOn (openCubeSet Q) (fun x k => mainFlatMinusCoordinate Q b L n (i,k) x) := by
  refine ⟨lambda8Q3GaussianModeParentPotential Q b L (mainFlatRotatedBasis i) n,?_⟩
  funext x k
  exact (old_signed_flat_minus_coordinate Q b L n i k x).symm

/-- Any honest representative of the actual Dirichlet projection has a
solenoidal residual. This is used to identify the physical plus field. -/
theorem old_signed_dirichlet_residual_solenoidal_of_gradient (Q : TriadicCube 2)
    {F : Vec 2 → Vec 2} (hF : MemVectorL2 (openCubeSet Q) F)
    (u : H10Function (openCubeSet Q))
    (hu : lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet Q)
      (toHilbertVectorL2OfVecField hF)=u.toH1Function.gradToHilbertVectorL2) :
    IsSolenoidalOn (openCubeSet Q) (fun x => F x-u.toH1Function.grad x) := by
  intro φ
  have h := lambda8DirichletProjection_residual_orthogonal
    (isOpenBoundedConvexDomain_openCubeSet Q) (toHilbertVectorL2OfVecField hF) φ
  rw [hu] at h
  simp only [H1Function.gradToHilbertVectorL2] at h
  rw [←toHilbertVectorL2OfVecField_sub hF u.toH1Function.grad_memVectorL2,
    inner_toHilbertVectorL2OfVecField_eq_integral] at h
  exact h

/-- The actual q3 parent residual is solenoidal on the same source square. -/
theorem old_signed_q3_parent_residual_solenoidal (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (v : Vec 2) (n : whiteBasisIndex) :
    IsSolenoidalOn (openCubeSet Q) (fun x =>
      q3Convolution b L h3Zero (whiteBasis n) x • v-
        (lambda8Q3GaussianModeParentPotential Q b L v n).toH1Function.grad x) := by
  have h := old_signed_dirichlet_residual_solenoidal_of_gradient Q
    (lambda8H1ComponentField_memVectorL2 (fun k => lambda8Q3GaussianModeLoadH1 Q b L v n k))
    (lambda8Q3GaussianModeParentPotential Q b L v n)
    (lambda8Q3GaussianModeParentPotential_spec Q b L v n).1
  exact h

end
end ASDExplicitGamma.Native
