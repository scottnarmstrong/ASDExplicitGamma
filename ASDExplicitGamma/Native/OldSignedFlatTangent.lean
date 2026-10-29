module

public import ASDExplicitGamma.Native.OldSignedNormalizedEnergy
public import ASDExplicitGamma.Native.OldSignedFlatBoundaryEnergy

/-! The exact negative flat tangent in AN (5.3), before any averaging in
the old coefficient. It combines with +y^2 to leave the boundary bill. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Scalar
noncomputable section

/-- The actual Dirichlet projection pairs with its source by its own
energy, retaining the parent zero-boundary condition. -/
theorem old_signed_dirichlet_source_pairing (Q : TriadicCube 2)
    (F : Vec 2 → Vec 2) (hF : MemVectorL2 (openCubeSet Q) F)
    (phi : H10Function (openCubeSet Q))
    (hsol : IsSolenoidalOn (openCubeSet Q) (fun x => F x-phi.toH1Function.grad x)) :
    volumeAverage (openCubeSet Q) (fun x => vecDot (F x) (phi.toH1Function.grad x))=
      ∑ k : Fin 2,energy Q (fun x => phi.toH1Function.grad x k) := by
  have h := hsol phi
  simp only [sub_eq_add_neg,vecDot_add_left,vecDot_neg_left] at h
  simp only [←sub_eq_add_neg] at h
  rw [integral_sub
    (integrableOn_vecDot_of_memVectorL2 hF phi.toH1Function.grad_memVectorL2)
    (integrableOn_vecDot_of_memVectorL2 phi.toH1Function.grad_memVectorL2 phi.toH1Function.grad_memVectorL2)] at h
  rw [←old_signed_vector_energy_normalization Q phi.toH1Function.grad_memVectorL2,
    ←real_inner_self_eq_norm_sq,inner_toHilbertVectorL2OfVecField_eq_integral]
  unfold volumeAverage
  rw [volume_openCubeSet_toReal]
  congr 1
  linarith

/-- The bottom affine flat pairing is exactly minus the Dirichlet energy,
for each actual white mode and canonical bottom load. -/
theorem old_signed_flat_minus_affine_pairing (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    volumeAverage (openCubeSet Q) (fun x => vecDot
      (q3Convolution b L h3Zero (whiteBasis n) x •
        matVecMul responsePlanarJ (fun k => mainFlatMinusCoordinate Q b L n (i,k) x)) (basisVec i))=
      -(∑ k : Fin 2,energy Q (fun x => mainFlatMinusCoordinate Q b L n (i,k) x)) := by
  let phi := lambda8Q3GaussianModeParentPotential Q b L (mainFlatRotatedBasis i) n
  have hg : phi.toH1Function.grad=fun x k => mainFlatMinusCoordinate Q b L n (i,k) x := by
    funext x k
    exact (old_signed_flat_minus_coordinate Q b L n i k x).symm
  have hh := old_signed_dirichlet_source_pairing Q
    (fun x => q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i)
    (old_signed_rotated_raw_load_memL2 Q b L (whiteBasis n) i) phi
    (old_signed_q3_parent_residual_solenoidal Q b L (mainFlatRotatedBasis i) n)
  rw [hg] at hh
  have he : (fun x => vecDot
      (q3Convolution b L h3Zero (whiteBasis n) x •
        matVecMul responsePlanarJ (fun k => mainFlatMinusCoordinate Q b L n (i,k) x)) (basisVec i))=
      fun x => -vecDot
        (q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i)
        (fun k => mainFlatMinusCoordinate Q b L n (i,k) x) := by
    funext x
    fin_cases i <;> simp [vecDot,matVecMul,responsePlanarJ,mainFlatRotatedBasis,basisVec,Fin.sum_univ_two]
  rw [he,volumeAverage,integral_neg]
  have hneg := congrArg Neg.neg hh
  unfold volumeAverage at hneg
  linarith only [hneg]

end
end ASDExplicitGamma.Native
