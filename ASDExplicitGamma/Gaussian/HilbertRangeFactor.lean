module

public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Analysis.Normed.Operator.Extend

/-! # Bounded images factored through the Hilbert closure of an actual covariance operator -/

@[expose] public section

open Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

section
variable {W H B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  (S : W →L[ℝ] H)

/-- The Hilbert closure keeps the ordinary H norm, rather than the covariance quotient norm. -/
noncomputable def hilbertRange : Submodule ℝ H := (LinearMap.range S.toLinearMap).topologicalClosure

noncomputable instance instHilbertRangeComplete [CompleteSpace H] : CompleteSpace (hilbertRange S) :=
  (LinearMap.range S.toLinearMap).isClosed_topologicalClosure.completeSpace_coe

noncomputable def hilbertRangeFactor : W →L[ℝ] hilbertRange S :=
  S.codRestrict (hilbertRange S) (fun x => subset_closure (show S x ∈ LinearMap.range S.toLinearMap from ⟨x, rfl⟩))

theorem hilbertRangeFactor_denseRange : DenseRange (hilbertRangeFactor S) := by
  have hd := ((denseRange_inclusion_iff (subset_closure : (Set.range S) ⊆ closure (Set.range S))).2
    (subset_rfl : closure (Set.range S) ⊆ closure (Set.range S))).comp
      (Set.rangeFactorization_surjective.denseRange)
      (continuous_inclusion (subset_closure : (Set.range S) ⊆ closure (Set.range S)))
  exact hd

/-- The bound is proved before extension; it forces every kernel element to have zero image. -/
noncomputable def hilbertRangeImage (T : W →L[ℝ] B) : hilbertRange S →L[ℝ] B :=
  T.toLinearMap.extendOfNorm (hilbertRangeFactor S).toLinearMap

theorem hilbertRangeImage_factor (T : W →L[ℝ] B)
    (hbound : ∃ C : ℝ, ∀ x, ‖T x‖ ≤ C * ‖S x‖) (x : W) :
    hilbertRangeImage S T (hilbertRangeFactor S x) = T x := by
  apply LinearMap.extendOfNorm_eq (hilbertRangeFactor_denseRange S)
  exact hbound

theorem hilbertRangeImage_norm_le (T : W →L[ℝ] B) (C : ℝ)
    (hbound : ∀ x, ‖T x‖ ≤ C * ‖S x‖) (x : hilbertRange S) :
    ‖hilbertRangeImage S T x‖ ≤ C * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le (hilbertRangeFactor_denseRange S) C hbound x

end
end ASDExplicitGamma.Gaussian
