module

public import ASDExplicitGamma.Native.ParentBoundaryInverseBulk
public import ASDExplicitGamma.Native.OldSignedDirichletLoadSymmetry

/-! Exact sign and rotation identities for the actual selected physical
Dirichlet gradients and harmonic boundary modes. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response
noncomputable section

/-- Selected potentials need not coincide pointwise, but their actual
Dirichlet gradients change sign almost everywhere, by projection linearity. -/
theorem parent_boundary_gradient_neg_ae (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (v : Vec 2) :
    (lambda8Q3GaussianModeParentPotential Q b L (-v) n).toH1Function.grad
      =ᵐ[normalizedCubeMeasure Q]
      fun x => -(lambda8Q3GaussianModeParentPotential Q b L v n).toH1Function.grad x := by
  have hh : (lambda8Q3GaussianModeParentPotential Q b L (-v) n).toH1Function.grad
      =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => -(lambda8Q3GaussianModeParentPotential Q b L v n).toH1Function.grad x := by
    have he := old_signed_q3_parent_gradient_neg Q b L n v
    filter_upwards [(lambda8Q3GaussianModeParentPotential Q b L (-v) n).toH1Function.coeFn_gradToHilbertVectorL2,
      (lambda8Q3GaussianModeParentPotential Q b L v n).toH1Function.coeFn_gradToHilbertVectorL2,
      Lp.coeFn_neg (lambda8Q3GaussianModeParentPotential Q b L v n).toH1Function.gradToHilbertVectorL2]
      with x hn hp hneg
    rw [he,hneg] at hn
    change -((lambda8Q3GaussianModeParentPotential Q b L v n).toH1Function.gradToHilbertVectorL2 x)=_ at hn
    rw [hp] at hn
    have ht := congrArg (HilbertVec.linearEquivVec 2) hn
    change HilbertVec.toVec (-HilbertVec.ofVec _) = HilbertVec.toVec (HilbertVec.ofVec _) at ht
    rw [←WithLp.toLp_neg,HilbertVec.toVec_ofVec,HilbertVec.toVec_ofVec] at ht
    exact ht.symm
  unfold normalizedCubeMeasure cubeMeasure
  apply Measure.ae_smul_measure
  rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  exact hh

/-- The four output-rotated plus remainders are a signed permutation of
the minus remainders on the same square and the SAME physical white mode. -/
theorem parent_boundary_remainder_mode_rotation (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) :
    ∀ᵐ x ∂normalizedCubeMeasure Q,∀ i k : Fin 2,
      matVecMul responsePlanarJ (fun l => oldSignedRemainderCoordinate Q b L true n (i,l) x) k =
        ∑ j : Fin 2,∑ l : Fin 2,responsePlanarJ k l *
          matVecMul responsePlanarJ (fun a => oldSignedRemainderCoordinate Q b L false n (j,a) x) l *
          responsePlanarJ j i := by
  filter_upwards [parent_boundary_gradient_neg_ae Q b L n (basisVec 0)] with x hx
  have hn (k : Fin 2) := congrFun hx k
  intro i k
  simp only [oldSignedRemainderCoordinate,Bool.false_eq_true,↓reduceIte,
    oldSignedFlatPlusRemainderCoordinateH1,oldSignedFlatMinusRemainderCoordinateH1,
    H1Function.sub_toFun,old_signed_complementary_coordinate_toFun,
    old_signed_rotated_projected_coordinate_toFun,old_signed_flat_minus_coordinate,
    old_signed_flat_plus_correction,old_signed_complementary_output_rotation]
  fin_cases i <;> fin_cases k
  all_goals norm_num [matVecMul,Fin.sum_univ_two,responsePlanarJ,
    old_signed_rotated_basis_zero,old_signed_rotated_basis_one,
    oldSignedRotatedProjectedField,hn,Pi.neg_apply]
  all_goals ring

end
end ASDExplicitGamma.Native
