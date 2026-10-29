module

public import ASDExplicitGamma.Cold.HistoryNormSplit
public import Mathlib.Algebra.Ring.GeomSum

/-! # Exact old-history algebra and the global strong-history branch -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The single alpha weight per depth becomes beta only on the fluctuation term. -/
theorem cold_old_history_algebra (α κ a S : ℝ) (j : ℕ) (E : ℕ → ℝ) :
    (1-α)*(∑ r ∈ Finset.range j, α^r*(a+κ^r*E r))+(α*κ)^j*S =
      (1-α^j)*a+(1-α)*(∑ r ∈ Finset.range j, (α*κ)^r*E r)+(α*κ)^j*S := by
  have he : (∑ r ∈ Finset.range j, α^r*(a+κ^r*E r)) =
      a*(∑ r ∈ Finset.range j, α^r)+(∑ r ∈ Finset.range j, (α*κ)^r*E r) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [mul_pow]
    ring
  rw [he]
  have hg := congrArg (fun x : ℝ => x*a) (geom_sum_mul_neg α j)
  nlinarith only [hg]

/-- A coarse root cap and genuine strong-sum tail preserve the global history cap. -/
theorem cold_global_history_algebra {α β R S : ℝ} (hβ : 0 ≤ β)
    (hcap : (1-α)*R ≤ (1-β)*S) (j : ℕ) :
    (1-α)*(∑ r ∈ Finset.range j, β^r*R)+β^j*S ≤ S := by
  have hsum : 0 ≤ ∑ r ∈ Finset.range j, β^r := Finset.sum_nonneg (fun r _ => pow_nonneg hβ r)
  have hm := mul_le_mul_of_nonneg_right hcap hsum
  have hg := geom_sum_mul_neg β j
  have he : (1-α)*(∑ r ∈ Finset.range j, β^r*R) =
      ((1-α)*R)*(∑ r ∈ Finset.range j, β^r) := by
    rw [← Finset.sum_mul]
    ring
  rw [he]
  have hgS := congrArg (fun x : ℝ => x*S) hg
  nlinarith only [hm,hgS]

end ASDExplicitGamma.Cold
