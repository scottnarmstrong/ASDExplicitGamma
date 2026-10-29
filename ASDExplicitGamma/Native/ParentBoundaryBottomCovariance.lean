module

public import ASDExplicitGamma.Native.ParentBoundaryInverseBulk
public import ASDExplicitGamma.Native.OldSignedBottomFlatPairing
public import ASDExplicitGamma.Native.OldSignedErrorProfiles

/-! Actual bottom signed covariance with the own-native Dirichlet
coefficient Y and centered same-cell reciprocal error charge. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic
noncomputable section

/-- The physical bottom term retains exactly -Y*(tr D-2), with the
actual centered beta and full reciprocal-gradient error on each cell. -/
theorem parent_boundary_bottom_covariance_bill (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 m
    let a := responseFramePlanarCoefficientField nu sigma k
    let f := fun n : whiteBasisIndex => 2*∑ i : Fin 2,
      (-oldSignedEnergyPairing Q nu sigma k
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,basisVec i))
        (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (oldSignedFlatMinusBlock Q b L n i))+
        ∑ j : Fin 2,energy Q (fun x => mainFlatMinusCoordinate Q b L n (i,j) x))
    Summable f ∧ (∑' n,f n)≤
      -parentBoundaryDirichletEnergy Q b L*(Matrix.trace (coarseBlockMatrix (openCubeSet Q) a).lowerRight-2)+
      2*descendantsAverage Q mesh (fun U =>
        parentBoundaryCenteredBeta Q U b L false*oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k) := by
  intro Q a f
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  have he : f=(fun n : whiteBasisIndex => 2*∑ i : Fin 2,∑ j : Fin 2,
      ∫ x,oldSignedBottomReciprocalError Q a hEll i x j*
        q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatMinusCoordinate Q b L n (i,l) x) j
          ∂normalizedCubeMeasure Q) := by
    funext n
    apply congrArg (fun t : ℝ => 2*t)
    apply Finset.sum_congr rfl
    intro i _
    rw [old_signed_actual_bottom_flat_pairing Q nu sigma hnu hsigma k b L n i]
    ring
  rw [he]
  have hb := parent_boundary_bottom_centered_feedback Q mesh a hEll b L
  rw [parent_boundary_signed_inverse_bulk m b L a] at hb
  refine ⟨(parent_boundary_bottom_centered_hasSum Q a hEll b L).summable,hb.trans ?_⟩
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  apply descendantsAverage_le
  intro U _
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  let v := fun c : BlockCoord 2 => vectorWeakHaarNorm U (fun x =>
    (blockMatVecMul (blockCoeffField a x)
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c) x)).2-(blockBasis c).2)^2
  change (∑ i : Fin 2,v (Sum.inr i))≤∑ c : BlockCoord 2,v c
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _))


end
end ASDExplicitGamma.Native
