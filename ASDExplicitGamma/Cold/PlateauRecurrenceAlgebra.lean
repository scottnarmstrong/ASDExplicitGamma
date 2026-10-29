module

public import ASDExplicitGamma.Cold.PlateauSeriesEnvelope
public import Mathlib.Tactic.Linarith

/-! # Finite-lag and infinite-tail assembly with one global bad-history charge -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Assemble an already proved finite-lag projection bound and its fine tail. The bad
sequence is summed across the two disjoint parts, so it is charged exactly once. -/
theorem plateau_series_split_bound {J : ℕ} {X C B μlag G : ℕ → ℝ} {μ α t : ℝ}
    (hX : Summable X) (hC : Summable C) (hB : Summable B)
    (hnear : ∀ k < J, X k ≤ 2*α*C k*(μlag k-μ)+(1+t)*G k+B k)
    (hfar : ∀ k, X (k+J) ≤ 2*C (k+J)*μ+B (k+J)) :
    (∑' k, X k) ≤ 2*α*(∑ k ∈ Finset.range J, C k*μlag k) -
      2*α*(∑ k ∈ Finset.range J, C k)*μ +
      (1+t)*(∑ k ∈ Finset.range J, G k) +
      2*(∑' k, C (k+J))*μ+(∑' k, B k) := by
  have hn := Finset.sum_le_sum (s := Finset.range J) (fun k hk => hnear k (Finset.mem_range.mp hk))
  have hct : Summable (fun k => C (k+J)) := (summable_nat_add_iff J).mpr hC
  have hbt : Summable (fun k => B (k+J)) := (summable_nat_add_iff J).mpr hB
  have hxt : Summable (fun k => X (k+J)) := (summable_nat_add_iff J).mpr hX
  have hf := hxt.tsum_le_tsum hfar (((hct.mul_left 2).mul_right μ).add hbt)
  rw [Summable.tsum_add ((hct.mul_left 2).mul_right μ) hbt,tsum_mul_right,tsum_mul_left] at hf
  have he : (∑ k ∈ Finset.range J, (2*α*C k*(μlag k-μ)+(1+t)*G k+B k)) =
      2*α*(∑ k ∈ Finset.range J, C k*μlag k)-2*α*(∑ k ∈ Finset.range J, C k)*μ+
      (1+t)*(∑ k ∈ Finset.range J, G k)+(∑ k ∈ Finset.range J, B k) := by
    have heach (k : ℕ) : 2*α*C k*(μlag k-μ)+(1+t)*G k+B k =
        (2*α)*(C k*μlag k)-(2*α*μ)*C k+(1+t)*G k+B k := by ring
    simp_rw [heach]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    ring
  rw [he] at hn
  have hx := hX.sum_add_tsum_nat_add J
  have hb := hB.sum_add_tsum_nat_add J
  linarith only [hn,hf,hx,hb]

/-- Rearranging the actual recovery inequality after the P5/P6 series assembly. -/
theorem plateau_recurrence_rearrange {J : ℕ} {X C B μlag G : ℕ → ℝ} {μ α t CT CD : ℝ}
    (hCT : 0 ≤ CT) (hX : Summable X) (hC : Summable C) (hB : Summable B)
    (hnear : ∀ k < J, X k ≤ 2*α*C k*(μlag k-μ)+(1+t)*G k+B k)
    (hfar : ∀ k, X (k+J) ≤ 2*C (k+J)*μ+B (k+J))
    (hrecovery : μ ≤ CT*(∑' k, X k)+CD*(μlag 1-μ)) :
    (1+2*CT*α*(∑ k ∈ Finset.range J, C k)+CD-2*CT*(∑' k, C (k+J)))*μ ≤
      2*CT*α*(∑ k ∈ Finset.range J, C k*μlag k)+CD*μlag 1+
      CT*(1+t)*(∑ k ∈ Finset.range J, G k)+CT*(∑' k, B k) := by
  have h := mul_le_mul_of_nonneg_left (plateau_series_split_bound hX hC hB hnear hfar) hCT
  nlinarith only [h,hrecovery]

/-- The source global bad charge is exactly 55/4, with no separate tail charge. -/
theorem plateau_bad_charge (CT g1 α H ξ : ℝ) :
    CT*(∑' k : ℕ, (2*g1*α*H^20/ξ^18)*(plateauEvenWeight k*(3:ℝ)^(k+1))) =
      (55/4)*CT*g1*α*H^20/ξ^18 := by
  rw [tsum_mul_left,tsum_plateauEvenWeight_three]
  ring

end ASDExplicitGamma.Cold
