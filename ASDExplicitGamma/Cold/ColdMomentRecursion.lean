module

public import ASDExplicitGamma.Cold.ColdMomentCaps
public import Mathlib.Probability.IdentDistrib

/-! # The strictly smaller-lag moment-cap recursion -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The actual source data for a same-law hierarchy of nonnegative trace defects.
The child arrays may be correlated across colours and across different parent lags. -/
structure ColdMomentSystem (Ω : Type*) [MeasurableSpace Ω] (ℙ : Measure Ω) where
  trace : ℕ → Ω → ℝ
  trace_memLp : ∀ ℓ, MemLp (trace ℓ) 20 ℙ
  trace_nonneg : ∀ ℓ, ∀ᵐ ω ∂ℙ, 0 ≤ trace ℓ ω
  children : ∀ k ℓ : ℕ, Fin (9^(ℓ-k)) → Ω → ℝ
  sameLaw : ∀ k ℓ i, ProbabilityTheory.IdentDistrib (children k ℓ i) (trace k) ℙ ℙ
  color : ∀ k ℓ : ℕ, Fin (9^(ℓ-k)) → Fin 4
  independent : ∀ k ℓ, k < ℓ → ∀ c, ProbabilityTheory.iIndepFun
    (fun i : {i // color k ℓ i = c} => children k ℓ i.val) ℙ
  subadditive : ∀ k ℓ, k < ℓ → ∀ᵐ ω ∂ℙ,
    trace ℓ ω ≤ (∑ i, children k ℓ i ω)/((9:ℝ)^(ℓ-k))

/-- One source moment update, deriving every child cap from its actual same-law trace. -/
theorem ColdMomentSystem.update {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (F : ColdMomentSystem Ω ℙ) {k ℓ : ℕ} (hkℓ : k < ℓ)
    {M D : ℝ} (hM : 0 ≤ M) (hcap : lpNorm (F.trace k) 20 ℙ ≤ M)
    (hmean : (∫ ω, F.trace k ω ∂ℙ) ≤ D) :
    lpNorm (F.trace ℓ) 20 ℙ ≤ min M (D+coldCenteredMomentCap M (ℓ-k)) := by
  have hn : Nonempty (Fin (9^(ℓ-k))) := Fin.pos_iff_nonempty.mp (pow_pos (by norm_num) _)
  let instColdMomentChildrenNonempty : Nonempty (Fin (9^(ℓ-k))) := hn
  have hm (i : Fin (9^(ℓ-k))) : MemLp (F.children k ℓ i) 20 ℙ :=
    (F.sameLaw k ℓ i).memLp_iff.mpr (F.trace_memLp k)
  have hnon (i : Fin (9^(ℓ-k))) : ∀ᵐ ω ∂ℙ, 0 ≤ F.children k ℓ i ω :=
    (F.sameLaw k ℓ i).symm.ae_mem_snd measurableSet_Ici (F.trace_nonneg k)
  have he (i : Fin (9^(ℓ-k))) : lpNorm (F.children k ℓ i) 20 ℙ = lpNorm (F.trace k) 20 ℙ :=
    congrArg ENNReal.toReal ((F.sameLaw k ℓ i).eLpNorm_eq (p := 20))
  have hmean' : (∑ i, ∫ ω, F.children k ℓ i ω ∂ℙ)/(Fintype.card (Fin (9^(ℓ-k))):ℝ) ≤ D := by
    simp_rw [(F.sameLaw k ℓ _).integral_eq]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [mul_div_cancel_left₀ _ (by positivity : ((9^(ℓ-k):ℕ):ℝ) ≠ 0)]
    exact hmean
  exact cold_moment_cap_update (F.color k ℓ) (Nat.sub_pos_of_lt hkℓ)
    (by simp only [Fintype.card_fin]) hm hnon (F.independent k ℓ hkℓ) hM
    (fun i => (he i).trans_le hcap) hmean' (F.trace_nonneg ℓ)
    (by simpa only [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using F.subadditive k ℓ hkℓ)

end ASDExplicitGamma.Cold
