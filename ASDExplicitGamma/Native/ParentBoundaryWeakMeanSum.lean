module

public import ASDExplicitGamma.Native.ParentBoundaryWeakMeanProfile

/-! Exact full-depth summation of the physical baseline-weighted weak mean slope. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Model Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- Exact affine-geometric source payment at the original weak discount. -/
def parentBoundaryWeakGeo (gamma growth : ℝ) (degree : ℕ) (U V : ℝ) : ℝ :=
  let q := parentBoundaryWeakRatio gamma growth degree
  U/(1-q)+V*q/(1-q)^2

/-- The closed source value of the full baseline-weighted mean slope. -/
def parentBoundaryWeakMeanSlope (gamma : ℝ) (height : ℕ) : ℝ :=
  let b : ℝ := 3683/2500
  let U := parentBoundaryCommonRawBase gamma height 5
  let V := 32474*gamma
  let F := parentBoundaryCommonRawFactor gamma height 5
  let K := parentBoundaryMeanKConstant*parentBoundaryCommonSourceSpatialClock gamma height 5 2
  let S := parentBoundaryCommonSourceVariance gamma height
  (1-inverseHistoryDiscount^2)*
    ((∑ i : Fin 3,parentBoundaryWeakMeanCoefficients gamma height i*b^3*F*
        parentBoundaryWeakGeo gamma 10 (i.val+2) U V)+
      (2*K*b^2*F)*parentBoundaryWeakGeo gamma 8 2 U V+
      (2*S*b^2)/(1-parentBoundaryWeakRatio gamma 4 0))

/-- The complete source depth program is summable and its exact sum is
the source's rational-geometric expression. No truncation is used. -/
theorem parent_boundary_weak_mean_profile_sum
    {gamma : ℝ} (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) (height : ℕ) :
    Summable (parentBoundaryWeakMeanDepthProfile gamma height) ∧
      (1-inverseHistoryDiscount^2)*(∑' j : ℕ,parentBoundaryWeakMeanDepthProfile gamma height j)=
        parentBoundaryWeakMeanSlope gamma height := by
  let b : ℝ := 3683/2500
  let U := parentBoundaryCommonRawBase gamma height 5
  let V := 32474*gamma
  let F := parentBoundaryCommonRawFactor gamma height 5
  let K := parentBoundaryMeanKConstant*parentBoundaryCommonSourceSpatialClock gamma height 5 2
  let S := parentBoundaryCommonSourceVariance gamma height
  let C := fun (i : Fin 3) (j : ℕ) => parentBoundaryWeakMeanCoefficients gamma height i*b^3*F*
    (parentBoundaryWeakRatio gamma 10 (i.val+2))^j*(U+V*(j:ℝ))
  have hc (i : Fin 3) : Summable (C i) := by
    exact ((parent_boundary_weak_affine_geometric gamma 10 U V (i.val+2) hg0 hg le_rfl).1.mul_left
      (parentBoundaryWeakMeanCoefficients gamma height i*b^3*F)).congr (fun j => by dsimp only [C]; ring)
  have hcs : Summable (fun j : ℕ => ∑ i : Fin 3,C i j) := summable_sum (fun i _ => hc i)
  have hm := (parent_boundary_weak_affine_geometric gamma 8 U V 2 hg0 hg (by norm_num)).1.mul_left (2*K*b^2*F)
  have hi := (summable_geometric_of_lt_one
    (parent_boundary_weak_ratio_range hg0 hg 4 (by norm_num) 0).1
    (parent_boundary_weak_ratio_range hg0 hg 4 (by norm_num) 0).2).mul_left (2*S*b^2)
  have hfull : Summable (parentBoundaryWeakMeanDepthProfile gamma height) := by
    exact ((hcs.add hm).add hi).congr (fun j => by
      dsimp only [parentBoundaryWeakMeanDepthProfile,C]
      ring)
  refine ⟨hfull,?_⟩
  have hefull : parentBoundaryWeakMeanDepthProfile gamma height=
      (fun j : ℕ => ((∑ i : Fin 3,C i j)+
        (2*K*b^2*F)*((parentBoundaryWeakRatio gamma 8 2)^j*(U+V*(j:ℝ))))+
          (2*S*b^2)*(parentBoundaryWeakRatio gamma 4 0)^j) := by
    funext j
    dsimp only [parentBoundaryWeakMeanDepthProfile,C]
    ring
  rw [hefull]
  rw [(hcs.add hm).tsum_add hi,hcs.tsum_add hm,Summable.tsum_finsetSum (fun i _ => hc i)]
  have hce (i : Fin 3) : (∑' j : ℕ,C i j)=parentBoundaryWeakMeanCoefficients gamma height i*b^3*F*
      parentBoundaryWeakGeo gamma 10 (i.val+2) U V := by
    have he : C i=(fun j : ℕ => (parentBoundaryWeakMeanCoefficients gamma height i*b^3*F)*
        ((parentBoundaryWeakRatio gamma 10 (i.val+2))^j*(U+V*(j:ℝ)))) := by funext j; dsimp only [C]; ring
    rw [he,tsum_mul_left,(parent_boundary_weak_affine_geometric gamma 10 U V (i.val+2) hg0 hg le_rfl).2]
    rfl
  simp_rw [hce]
  rw [tsum_mul_left,tsum_mul_left,
    (parent_boundary_weak_affine_geometric gamma 8 U V 2 hg0 hg (by norm_num)).2,
    tsum_geometric_of_lt_one
      (parent_boundary_weak_ratio_range hg0 hg 4 (by norm_num) 0).1
      (parent_boundary_weak_ratio_range hg0 hg 4 (by norm_num) 0).2]
  rfl

/-- The literal baseline-weighted actual depth slopes have the complete
source sum, retaining all physical-frame and weak weights. -/
theorem parent_boundary_weak_mean_slope_sum
    (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (height : ℕ) :
    Summable (fun j : ℕ => (3683/2500:ℝ)*inverseHistoryDiscount^(2*j)*
      (3:ℝ)^(2*M.gamma*(j:ℝ))*parentBoundaryMeanDepthSlope M.gamma height j) ∧
      (1-inverseHistoryDiscount^2)*(∑' j : ℕ,(3683/2500:ℝ)*inverseHistoryDiscount^(2*j)*
        (3:ℝ)^(2*M.gamma*(j:ℝ))*parentBoundaryMeanDepthSlope M.gamma height j)=
          parentBoundaryWeakMeanSlope M.gamma height := by
  simp_rw [parent_boundary_weak_mean_depth_profile_eq]
  exact parent_boundary_weak_mean_profile_sum M.shellPrefix.gamma_pos.le hg height

end
end ASDExplicitGamma.Native
