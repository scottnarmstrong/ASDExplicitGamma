module

public import ASDExplicitGamma.Cold.HistorySeriesAlgebra
public import ASDExplicitGamma.Cold.LpMonotonicity

/-! # The complete source L20 history and a genuine strong-sum fine tail -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Norm of a scalar multiple in the form used for history depths. -/
theorem cold_lpNorm_nonneg_mul {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    (f : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    lpNorm (fun ω => c*f ω) 20 ℙ = c*lpNorm f 20 ℙ := by
  have he : (fun ω => c*f ω) = c • f := rfl
  rw [he,lpNorm_const_smul]
  simp only [Real.nnnorm_of_nonneg hc,NNReal.coe_mk]

/-- Norm-sum tails are bounded directly by the genuine strong sum. -/
theorem cold_history_norm_tail {b root : ℕ → ℝ} {α β κ S : ℝ} {j : ℕ}
    (hβ : 0 ≤ β) (hrel : α*κ = β) (hb : ∀ r, 0 ≤ b r)
    (hStrong : Summable (fun k => (1-α)*β^k*root k))
    (hS : (∑' k, (1-α)*β^k*root k) ≤ S)
    (hcap : ∀ k, b (k+j) ≤ (1-α)*α^(k+j)*(κ^(k+j)*root k)) :
    Summable b ∧ (∑' k, b (k+j)) ≤ β^j*S := by
  have hd (k : ℕ) : b (k+j) ≤ β^j*((1-α)*β^k*root k) := by
    have he : (1-α)*α^(k+j)*(κ^(k+j)*root k) = β^j*((1-α)*β^k*root k) := by
      calc
        _ = (1-α)*(α*κ)^(k+j)*root k := by rw [mul_pow]; ring
        _ = _ := by rw [hrel,pow_add]; ring
    exact (hcap k).trans_eq he
  have hs : Summable (fun k => b (k+j)) := Summable.of_nonneg_of_le (fun k => hb _) hd
    (hStrong.mul_left (β^j))
  refine ⟨(summable_nat_add_iff j).mp hs,?_⟩
  have h := hs.tsum_le_tsum hd (hStrong.mul_left (β^j))
  rw [tsum_mul_left] at h
  exact h.trans (mul_le_mul_of_nonneg_left hS (pow_nonneg hβ _))

/-- Every complete pointwise history has the finite-prefix plus genuine-fine-tail cap.
The hypotheses concern individual depth norms and the native strong sum; the L20
history cap and its series convergence are conclusions. -/
theorem cold_complete_history_norm_split {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {M : ℕ → Ω → ℝ} {C root : ℕ → ℝ} {α β κ S : ℝ} {j : ℕ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hβ : 0 ≤ β) (hrel : α*κ = β)
    (hM : ∀ r, MemLp (M r) 20 ℙ)
    (hStrong : Summable (fun k => (1-α)*β^k*root k))
    (hS : (∑' k, (1-α)*β^k*root k) ≤ S)
    (hnear : ∀ r < j, lpNorm (M r) 20 ℙ ≤ C r)
    (hfar : ∀ k, lpNorm (M (k+j)) 20 ℙ ≤ κ^(k+j)*root k) :
    MemLp (fun ω => coldWeightedHistory α (fun r => M r ω)) 20 ℙ ∧
      lpNorm (fun ω => coldWeightedHistory α (fun r => M r ω)) 20 ℙ ≤
        (1-α)*(∑ r ∈ Finset.range j, α^r*C r)+β^j*S := by
  let b := fun r => (1-α)*α^r*lpNorm (M r) 20 ℙ
  have hb (r : ℕ) : 0 ≤ b r := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hα1) (pow_nonneg hα _)) lpNorm_nonneg
  have ht := cold_history_norm_tail hβ hrel hb hStrong hS (fun k =>
    mul_le_mul_of_nonneg_left (hfar k) (mul_nonneg (sub_nonneg.mpr hα1) (pow_nonneg hα _)))
  have hmf (r : ℕ) : MemLp (fun ω => ((1-α)*α^r)*M r ω) 20 ℙ := (hM r).const_mul _
  obtain ⟨hmem,hbound⟩ := cold_lpNorm_twenty_tsum_le hmf ht.1 (fun r => by
    rw [cold_lpNorm_nonneg_mul _ (mul_nonneg (sub_nonneg.mpr hα1) (pow_nonneg hα _))])
  have he : (fun ω => ∑' r, ((1-α)*α^r)*M r ω) =
      (fun ω => coldWeightedHistory α (fun r => M r ω)) := by
    funext ω
    simp only [coldWeightedHistory,← tsum_mul_left,mul_assoc]
  rw [he] at hmem hbound
  refine ⟨hmem,?_⟩
  have hn := Finset.sum_le_sum (s := Finset.range j) (fun r hr =>
    mul_le_mul_of_nonneg_left (hnear r (Finset.mem_range.mp hr))
      (mul_nonneg (sub_nonneg.mpr hα1) (pow_nonneg hα r)))
  have heq : (∑ r ∈ Finset.range j, (1-α)*α^r*C r) =
      (1-α)*(∑ r ∈ Finset.range j, α^r*C r) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [heq] at hn
  have hsplit := ht.1.sum_add_tsum_nat_add j
  linarith only [hbound,hn,ht.2,hsplit]

end ASDExplicitGamma.Cold
