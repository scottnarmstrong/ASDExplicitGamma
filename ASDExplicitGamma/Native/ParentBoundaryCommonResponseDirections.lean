module

public import ASDExplicitGamma.Gaussian.SquareDirections
public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterHilbertTrace

/-! Actual globally indexed common-center response directions on any square. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Model Response Triadic Variational Inverse
noncomputable section

/-- Restrict the global convolution to Q and subtract its value at the one
original source center P. The same white-noise enumeration is used everywhere. -/
def parentBoundaryCommonResponseDirections (P Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : ℕ) : ResponseCoefficient (openCubeSet Q) :=
  squareQ3Directions Q b L n - BoundedContinuousFunction.const _
    (q3Convolution b L h3Zero (gaussEnumerated whiteBasis n) (cubeCenter P))

/-- The actual common-center response direction has its literal physical value. -/
theorem parent_boundary_common_response_direction_value
    (P Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) (n : ℕ)
    {x : Vec 2} (hx : x ∈ openCubeSet Q) :
    responseCoefficientExtension (parentBoundaryCommonResponseDirections P Q b L n) x =
      q3Convolution b L h3Zero (gaussEnumerated whiteBasis n) x -
        q3Convolution b L h3Zero (gaussEnumerated whiteBasis n) (cubeCenter P) := by
  rw [responseCoefficientExtension_eq _ hx]
  rfl

/-- The common-center direction is divided by the true response frame. -/
theorem parent_boundary_common_response_direction_frame
    (P Q : TriadicCube 2) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (l : whiteBasisIndex) :
    (parentBoundaryCommonBasisMultiplier P Q b σ L l).toFun =ᵐ[
      volume.restrict (openCubeSet Q)] fun x => responseCoefficientExtension
        (parentBoundaryCommonResponseDirections P Q b L
          (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)) x / σ := by
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
  rw [parent_boundary_common_response_direction_value P Q b L _ hx,enumerated_encode]
  simp only [parentBoundaryCommonBasisMultiplier,H1Function.smul_toFun,
    parent_boundary_common_q3_direction_value,smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- The complete actual common-center direction family has square-summable
continuous norms. The center can be outside the observed square. -/
theorem parent_boundary_common_response_directions_summable
    (P Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    Summable (fun n => ‖parentBoundaryCommonResponseDirections P Q b L n‖^2) := by
  obtain ⟨m,hm⟩ := exists_originCube_containing_compact
    (closure (openCubeSet Q) ∪ {cubeCenter P})
    ((isBounded_openCubeSet Q).isCompact_closure.union isCompact_singleton)
  have hpoint (n : ℕ) {x : Vec 2} (hx : x ∈ openCubeSet (originCube 2 m)) :
      ‖q3Convolution b L h3Zero (gaussEnumerated whiteBasis n) x‖ ≤
        ‖pureFluxMainCubeQ3ResponseCoefficient m b L n‖ := by
    have hv := pureFluxMainCubeQ3ResponseCoefficient_value m b L n hx
    rw [mainQ3DirectionW2_value] at hv
    rw [← hv]
    have h := (responseCoefficientExtension (pureFluxMainCubeQ3ResponseCoefficient m b L n)).norm_coe_le_norm x
    simpa only [responseCoefficientExtension_norm] using h
  have hnorm (n : ℕ) : ‖parentBoundaryCommonResponseDirections P Q b L n‖ ≤
      2*‖pureFluxMainCubeQ3ResponseCoefficient m b L n‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro x
    change ‖q3Convolution b L h3Zero (gaussEnumerated whiteBasis n) x.val -
      q3Convolution b L h3Zero (gaussEnumerated whiteBasis n) (cubeCenter P)‖ ≤ _
    exact (norm_sub_le _ _).trans ((add_le_add
      (hpoint n (hm (Or.inl x.property)))
      (hpoint n (hm (Or.inr (Set.mem_singleton _))))).trans_eq (by ring))
  have hs := (main_q3_responseCoefficient_summable m b L).mul_left (4:ℝ)
  apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ hs
  intro n
  have hh := pow_le_pow_left₀ (norm_nonneg _) (hnorm n) 2
  simpa only [mul_pow,show (2:ℝ)^2=4 by norm_num] using hh

/-- The zero padding is removed exactly, with no finite covariance truncation. -/
theorem parent_boundary_common_response_directions_tsum
    (P Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (f : ResponseCoefficient (openCubeSet Q) → ℝ) (hf : f 0=0) :
    (∑' n,f (parentBoundaryCommonResponseDirections P Q b L n)) =
      ∑' l : whiteBasisIndex,f (parentBoundaryCommonResponseDirections P Q b L
        (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)) := by
  classical
  let enc := @Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex)
  let v := fun l => parentBoundaryCommonResponseDirections P Q b L (enc l)
  have hz (n : ℕ) (hn : n ∉ Set.range enc) : parentBoundaryCommonResponseDirections P Q b L n=0 := by
    ext x
    change q3Convolution b L h3Zero (gaussEnumerated whiteBasis n) x.val -
      q3Convolution b L h3Zero (gaussEnumerated whiteBasis n) (cubeCenter P)=0
    rw [gaussEnumerated,Function.extend_apply' _ _ _ hn]
    simp only [q3Convolution,Pi.zero_apply,inner_zero_left,sub_self]
  have heq (n : ℕ) : parentBoundaryCommonResponseDirections P Q b L n=gaussEnumerated v n := by
    by_cases hn : n ∈ Set.range enc
    · obtain ⟨l,rfl⟩ := hn
      rw [enumerated_encode]
    · rw [hz n hn,gaussEnumerated,Function.extend_apply' _ _ _ hn]
      rfl
  simp_rw [heq]
  simpa only [enumerated_encode] using enumerated_tsum_apply v f hf

end
end ASDExplicitGamma.Native
