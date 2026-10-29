module

public import ASDExplicitGamma.Native.ParentBoundarySourceBudget
public import ASDExplicitGamma.Native.OldSignedErrorProfiles

/-! The complete parent-source size has the sharp broken weak-profile
bound on the same physical finite partition. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational
noncomputable section

/-- Source (3.1), summed over all four ACTUAL parent minimizers and all
physical covariance modes. The comparison depth is independent of the
parent interpolant, and no source-profile cap is assumed. -/
theorem parent_boundary_source_profile (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    descendantsAverage Q depth (fun U => parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L^2) ≤
      parentBoundaryPotentialSourceClock Q depth b L^2*
        descendantsAverage Q depth (fun U => oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k^2) := by
  let p := fun (n : whiteBasisIndex) (c : BlockCoord 2) (U : TriadicCube 2) =>
    vectorPositiveHaarNorm U (fun x => (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (blockBasis c) x).2)^2
  let f := fun n U => ∑ c : BlockCoord 2,p n c U
  have hss (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) : Summable (fun n => f n U) :=
    parent_boundary_cell_source_series Q U depth hU nu sigma hnu hsigma k b L
  have hpart := (old_signed_partition_series Q depth f hss).2
  have hleft : descendantsAverage Q depth (fun U => parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L^2)=
      ∑' n,descendantsAverage Q depth (f n) := by
    rw [hpart]
    apply congrArg (descendantsAverage Q depth)
    funext U
    exact Real.sq_sqrt (tsum_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  let u := fun c : BlockCoord 2 => oldSignedCanonicalFirstCorrector Q (responseFramePlanarCoefficientField nu sigma k)
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q) nu sigma hnu hsigma k) (blockBasis c)
  have hs (c : BlockCoord 2) : Summable (fun n : whiteBasisIndex => descendantsAverage Q depth (p n c)) :=
    (parent_boundary_actual_source_trace Q depth nu sigma hnu hsigma k (blockBasis c) b L).1
  have havg (n : whiteBasisIndex) : descendantsAverage Q depth (f n)=
      ∑ c : BlockCoord 2,descendantsAverage Q depth (p n c) :=
    Homogenization.descendantsAverage_sum Q depth Finset.univ (fun U c => p n c U)
  rw [hleft]
  simp_rw [havg]
  rw [Summable.tsum_finsetSum (fun c _ => hs c)]
  have hbound := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    (parent_boundary_actual_source_trace Q depth nu sigma hnu hsigma k (blockBasis c) b L).2)
  apply hbound.trans_eq
  rw [←Finset.mul_sum]
  apply congrArg (fun z : ℝ => parentBoundaryPotentialSourceClock Q depth b L^2*z)
  have hg (c : BlockCoord 2) : (u c).toH1Function.grad=fun x =>
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c) x).1-(blockBasis c).1 :=
    old_signed_canonical_first_corrector_grad Q _ _ (blockBasis c)
  change (∑ c : BlockCoord 2,lemmaVTiledWeakEnergy Q depth (u c).toH1Function.grad)=_
  simp only [lemmaVTiledWeakEnergy,hg]
  rw [←Homogenization.descendantsAverage_sum]
  apply congrArg (descendantsAverage Q depth)
  funext U
  unfold oldSignedPrimalErrorSize
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  have hnorm (F : Vec 2 → Vec 2) : vectorWeakHaarNorm U F^2=vectorWeakHaarEnergy U F :=
    Real.sq_sqrt (vectorWeakHaarEnergy_nonneg U F)
  simp only [hnorm]

end
end ASDExplicitGamma.Native
