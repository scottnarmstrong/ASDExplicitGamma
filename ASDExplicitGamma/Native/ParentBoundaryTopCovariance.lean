module

public import ASDExplicitGamma.Native.ParentBoundaryTopPairing
public import ASDExplicitGamma.Native.ParentBoundaryFeedback
public import ASDExplicitGamma.Native.OldSignedErrorProfiles

/-! Actual parent-source top covariance charge with the COMPLETE centered
contraction and the same physical parent first-gradient errors. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic
noncomputable section

/-- The physical top-flat/parent-source cross has the sharp centered beta
charge, with all common-noise sums genuinely convergent. -/
theorem parent_boundary_top_covariance_bill (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let f := fun n : whiteBasisIndex => 2*∑ i : Fin 2,volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatPlusBlock Q b L n i x).2
        (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (basisVec i,0) x).2)
    Summable f ∧ |∑' n,f n|≤2*descendantsAverage Q depth (fun U =>
      parentBoundaryCenteredBeta Q U b L true*oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k) := by
  intro f
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  let g := fun n : whiteBasisIndex => 2*∑ i : Fin 2,∑ j : Fin 2,
    ∫ x,oldSignedTopPrimalError Q a hEll i x j*
      q3Convolution b L h3Zero (whiteBasis n) x*
      matVecMul responsePlanarJ (fun l => mainFlatPlusCoordinate Q b L n (i,l) x) j ∂normalizedCubeMeasure Q
  have hf : f=fun n => -g n := by
    funext n
    simp only [f,g,parent_boundary_top_flat_pairing,Finset.sum_neg_distrib]
    ring
  have hs : Summable g := (parent_boundary_top_centered_hasSum Q a hEll b L).summable
  rw [hf]
  refine ⟨hs.neg,?_⟩
  rw [tsum_neg,abs_neg]
  have hb := parent_boundary_top_centered_feedback Q depth a hEll b L
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  unfold descendantsAverage
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro U _
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  let v := fun c : BlockCoord 2 => vectorWeakHaarNorm U (fun x =>
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c) x).1-(blockBasis c).1)^2
  change (∑ i : Fin 2,v (Sum.inl i))≤∑ c : BlockCoord 2,v c
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end
end ASDExplicitGamma.Native
