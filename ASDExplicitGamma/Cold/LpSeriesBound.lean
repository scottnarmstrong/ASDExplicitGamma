module

public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # The actual L20 history series from summable depth-norm caps -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- Summable L20 caps bound the actual pointwise series and establish its L20 membership. -/
theorem cold_lpNorm_twenty_tsum_le {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {F : ℕ → Ω → ℝ} {b : ℕ → ℝ} (hF : ∀ r, MemLp (F r) 20 ℙ)
    (hb : Summable b) (hcap : ∀ r, lpNorm (F r) 20 ℙ ≤ b r) :
    MemLp (fun ω => ∑' r, F r ω) 20 ℙ ∧
      lpNorm (fun ω => ∑' r, F r ω) 20 ℙ ≤ ∑' r, b r := by
  let instColdSeriesFactTwenty : Fact ((1:ℝ≥0∞) ≤ 20) := ⟨by norm_num⟩
  let Z := fun r => (hF r).toLp (F r)
  have hz (r : ℕ) : ‖Z r‖ = lpNorm (F r) 20 ℙ := Lp.norm_toLp _ _
  have hnorm : Summable (fun r => ‖Z r‖) :=
    Summable.of_nonneg_of_le (fun r => norm_nonneg (Z r)) (fun r => by rw [hz]; exact hcap r) hb
  have henorm : (∑' r, ‖Z r‖ₑ) ≠ ⊤ := by
    exact tsum_enorm_ne_top_iff_summable_norm.mpr hnorm
  have hae : (fun ω => (∑' r, Z r) ω) =ᵐ[ℙ] (fun ω => ∑' r, F r ω) := by
    have h := Lp.coeFn_tsum henorm
    filter_upwards [h,ae_all_iff.mpr (fun r => (hF r).coeFn_toLp)] with ω hω hfω
    rw [hω]
    exact tsum_congr (fun r => hfω r)
  have hmem := (Lp.memLp (∑' r, Z r)).ae_eq hae
  refine ⟨hmem,?_⟩
  have hnormsum := norm_tsum_le_tsum_norm hnorm
  have hbound := hnorm.tsum_le_tsum (fun r => by rw [hz]; exact hcap r) hb
  have he : lpNorm (fun ω => ∑' r, F r ω) 20 ℙ = ‖∑' r, Z r‖ := by
    rw [← toReal_eLpNorm,← eLpNorm_congr_ae hae]
    rfl
  rw [he]
  exact hnormsum.trans hbound

/-- Summable depth-norm caps also give absolute pointwise convergence almost everywhere. -/
theorem cold_lpNorm_twenty_summable_ae {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {F : ℕ → Ω → ℝ} {b : ℕ → ℝ} (hF : ∀ r, MemLp (F r) 20 ℙ)
    (hb : Summable b) (hcap : ∀ r, lpNorm (F r) 20 ℙ ≤ b r) :
    ∀ᵐ ω ∂ℙ, Summable (fun r => ‖F r ω‖) := by
  have hnorm : Summable (fun r => lpNorm (F r) 20 ℙ) :=
    Summable.of_nonneg_of_le (fun _ => lpNorm_nonneg) hcap hb
  have henorm : (∑' r, eLpNorm (F r) 20 ℙ) ≠ ⊤ := by
    have he : (fun r => eLpNorm (F r) 20 ℙ) =
        (fun r => ENNReal.ofReal (lpNorm (F r) 20 ℙ)) := by
      funext r
      rw [← toReal_eLpNorm,ENNReal.ofReal_toReal (hF r).eLpNorm_ne_top]
    rw [he]
    exact ne_of_lt hnorm.tsum_ofReal_lt_top
  exact summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞) ≤ 20) henorm

end ASDExplicitGamma.Cold
