module

public import ASDExplicitGamma.Native.OldSignedDirichletLoadSymmetry
public import ASDExplicitGamma.Native.OldSignedMinusRemainderEnergy

/-! The zero-normal field removed from the plus load has the same full
two-load energy as the minus Dirichlet field, with the source signs retained. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Response
noncomputable section

/-- Normalized parent Dirichlet energy is invariant under a load sign. -/
theorem old_signed_q3_parent_energy_neg (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (v : Vec 2) :
    (∑ k : Fin 2,energy Q (fun x =>
      (lambda8Q3GaussianModeParentPotential Q b L (-v) n).toH1Function.grad x k)) =
    ∑ k : Fin 2,energy Q (fun x =>
      (lambda8Q3GaussianModeParentPotential Q b L v n).toH1Function.grad x k) := by
  rw [←old_signed_vector_energy_normalization Q
    (lambda8Q3GaussianModeParentPotential Q b L (-v) n).toH1Function.grad_memVectorL2,
    ←old_signed_vector_energy_normalization Q
      (lambda8Q3GaussianModeParentPotential Q b L v n).toH1Function.grad_memVectorL2]
  change (cubeVolume Q)⁻¹*‖(lambda8Q3GaussianModeParentPotential Q b L (-v) n).toH1Function.gradToHilbertVectorL2‖^2=_
  rw [old_signed_q3_parent_gradient_neg,norm_neg]
  rfl

/-- Summing both loads removes the input quarter turn from the actual
Dirichlet energy, including the negative second load. -/
theorem old_signed_q3_parent_two_load_energy (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    oldSignedFlatDirichletModeEnergy Q b L n=
      ∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x =>
        (lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad x k) := by
  unfold oldSignedFlatDirichletModeEnergy
  simp_rw [old_signed_flat_minus_coordinate]
  conv_lhs => rw [Fin.sum_univ_two]
  conv_rhs => rw [Fin.sum_univ_two]
  rw [old_signed_rotated_basis_zero,old_signed_rotated_basis_one,old_signed_q3_parent_energy_neg]
  exact add_comm _ _

/-- The actual zero-normal correction removed from the plus field. -/
def oldSignedFlatRemovedField (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) : Vec 2 → Vec 2 :=
  fun x => q3Convolution b L h3Zero (whiteBasis n) x • mainFlatRotatedBasis i-
    (fun k => mainFlatPlusCoordinate Q b L n (i,k) x)

/-- The removed field is the positively rotated actual parent gradient. -/
theorem old_signed_flat_removed_field (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    oldSignedFlatRemovedField Q b L n i=fun x => matVecMul responsePlanarJ
      ((lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad x) := by
  funext x k
  simp only [oldSignedFlatRemovedField,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    old_signed_flat_plus_coordinate]
  ring

/-- The actual two-load zero-normal removed energy equals the actual
Dirichlet two-load energy, pointwise in the full white-mode family. -/
theorem old_signed_flat_removed_energy_sum (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) :
    (∑ i : Fin 2,∑ k : Fin 2,energy Q (fun x => oldSignedFlatRemovedField Q b L n i x k))=
      oldSignedFlatDirichletModeEnergy Q b L n := by
  rw [old_signed_q3_parent_two_load_energy]
  apply Finset.sum_congr rfl
  intro i _
  have h0 : (fun x => oldSignedFlatRemovedField Q b L n i x 0)=fun x =>
      -(lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad x 1 := by
    funext x
    rw [old_signed_flat_removed_field]
    norm_num [matVecMul,responsePlanarJ,Fin.sum_univ_two]
  have h1 : (fun x => oldSignedFlatRemovedField Q b L n i x 1)=fun x =>
      (lambda8Q3GaussianModeParentPotential Q b L (basisVec i) n).toH1Function.grad x 0 := by
    funext x
    rw [old_signed_flat_removed_field]
    norm_num [matVecMul,responsePlanarJ,Fin.sum_univ_two]
  rw [Fin.sum_univ_two,h0,h1,energy_neg,Fin.sum_univ_two]
  ring

end
end ASDExplicitGamma.Native
