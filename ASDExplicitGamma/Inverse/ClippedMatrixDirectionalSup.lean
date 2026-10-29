module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-! Positive directional deviations on one fixed loading population. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open scoped NNReal

/-- A unit-vector quadratic form is bounded by the genuine operator norm. -/
theorem clipped_unit_quadratic_abs_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E) (x : E) (hx : ‖x‖=1) :
    |inner ℝ x (T x)| ≤ ‖T‖ := by
  have hh := (norm_inner_le_norm (𝕜 := ℝ) x (T x)).trans
    (mul_le_mul_of_nonneg_left (T.le_opNorm x) (norm_nonneg x))
  simpa only [Real.norm_eq_abs,hx,one_mul,mul_one] using hh

/-- The positive largest directional deviation over any fixed nonempty unit
population is one-Lipschitz in the Euclidean operator norm. In particular it
is measurable without enumerating directions or choosing exceptional sets. -/
theorem clipped_positive_directional_sup_lipschitz {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Set E) (hne : S.Nonempty)
    (hunit : ∀ x ∈ S, ‖x‖=1) :
    LipschitzWith 1 (fun T : E →L[ℝ] E => max 0 (sSup ((fun x => inner ℝ x (T x)) '' S))) := by
  have hb (T : E →L[ℝ] E) : BddAbove ((fun x => inner ℝ x (T x)) '' S) := by
    refine ⟨‖T‖,?_⟩
    rintro a ⟨x,hx,rfl⟩
    exact (le_abs_self _).trans (clipped_unit_quadratic_abs_le T x (hunit x hx))
  have hs (T U : E →L[ℝ] E) : sSup ((fun x => inner ℝ x (T x)) '' S) ≤
      sSup ((fun x => inner ℝ x (U x)) '' S)+‖T-U‖ := by
    apply csSup_le (hne.image _)
    rintro a ⟨x,hx,rfl⟩
    have hdiff := clipped_unit_quadratic_abs_le (T-U) x (hunit x hx)
    have hle := le_csSup (hb U) (Set.mem_image_of_mem (fun y => inner ℝ y (U y)) hx)
    have he : inner ℝ x ((T-U) x) = inner ℝ x (T x)-inner ℝ x (U x) := by
      simp only [sub_apply,inner_sub_right]
    rw [he] at hdiff
    have hupper := (abs_le.mp hdiff).2
    linarith only [hle,hupper]
  have hm (T U : E →L[ℝ] E) : max 0 (sSup ((fun x => inner ℝ x (T x)) '' S)) ≤
      max 0 (sSup ((fun x => inner ℝ x (U x)) '' S))+‖T-U‖ := by
    apply max_le
    · exact add_nonneg (le_max_left _ _) (norm_nonneg _)
    · exact (hs T U).trans (add_le_add (le_max_right _ _) le_rfl)
  apply LipschitzWith.of_dist_le_mul
  intro T U
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  apply abs_le.mpr
  have h1 := hm T U
  have h2 := hm U T
  rw [norm_sub_rev U T] at h2
  constructor <;> linarith only [h1,h2]

/-- The same positive deviation is bounded by the operator norm. -/
theorem clipped_positive_directional_sup_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (S : Set E) (hne : S.Nonempty)
    (hunit : ∀ x ∈ S, ‖x‖=1) (T : E →L[ℝ] E) :
    max 0 (sSup ((fun x => inner ℝ x (T x)) '' S)) ≤ ‖T‖ := by
  apply max_le (norm_nonneg _)
  apply csSup_le (hne.image _)
  rintro a ⟨x,hx,rfl⟩
  exact (le_abs_self _).trans (clipped_unit_quadratic_abs_le T x (hunit x hx))

end ASDExplicitGamma.Inverse
