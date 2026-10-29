module

public import ASDExplicitGamma.Cold.HistoryCapAlgebra
public import ASDExplicitGamma.Cold.HistoryParameters
public import ASDExplicitGamma.Cold.HistoryOldFluctuation

/-! # CO-COLD-HISTORY-CAPS: all three complete-history candidates -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

instance instColdHistoryNinePowNonempty (r : ℕ) : Nonempty (Fin (9^r)) :=
  ⟨⟨0,pow_pos (by norm_num) _⟩⟩

/-- The exact old-history branch, including the complete fine strong-sum tail. -/
def coldOldHistoryCap (a R S : ℝ) (j : ℕ) : ℝ :=
  (1-coldHistoryAlpha^j)*a+(1-coldHistoryAlpha)*R*
    (∑ r ∈ Finset.range j, coldHistoryBeta^r*
      min 1 (4*Real.sqrt 19*(3:ℝ)^(-((j-r:ℕ):ℝ))))+coldHistoryBeta^j*S

/-- The exact corrected triangular history cap. -/
def coldTriangularHistoryCap (M D : ℕ → ℝ) (a R S : ℝ) (j : ℕ) : ℝ :=
  min S (min (coldOldHistoryCap a R S j)
    ((1-coldHistoryAlpha)*(∑ r ∈ Finset.range j, coldHistoryAlpha^r*coldHistoryDepthCap M D j r)+
      coldHistoryBeta^j*S))

/-- CO-COLD-HISTORY-CAPS for the actual cell arrays. Per-cell source moment and
positive-fluctuation caps and the genuine native strong sum imply the complete history
bound. No maximum cap, independence between optimizers and blocks, truncated history,
or assumption restating the history conclusion occurs. -/
theorem cold_history_caps {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (X : ∀ r : ℕ, Fin (9^r) → Ω → ℝ) {M D root : ℕ → ℝ}
    {a R S : ℝ} {j : ℕ} (ha : 0 ≤ a) (hR : 0 ≤ R) (hM : ∀ ℓ, 0 ≤ M ℓ)
    (hD : ∀ k, 0 ≤ D k) (hM0 : M 0 = R) (hD0 : D 0 ≤ a) (hMR : ∀ ℓ, M ℓ ≤ R)
    (hglobal : (1-coldHistoryAlpha)*R ≤ (1-coldHistoryBeta)*S)
    (hX : ∀ r i, MemLp (X r i) 20 ℙ) (hMeas : ∀ r i, Measurable (X r i))
    (hn : ∀ r i, ∀ᵐ ω ∂ℙ, 0 ≤ X r i ω)
    (hraw : ∀ r < j, ∀ i, lpNorm (X r i) 20 ℙ ≤ M (j-r))
    (hfluct : ∀ r < j, ∀ k ∈ coldHistoryEarlierLags j r, ∀ i,
      lpNorm (fun ω => max (X r i ω-D k) 0) 20 ℙ ≤ coldCenteredMomentCap (M k) (j-r-k))
    (hfar : ∀ k i, lpNorm (X (k+j) i) 20 ℙ ≤ root k)
    (hStrong : Summable (fun k => (1-coldHistoryAlpha)*coldHistoryBeta^k*root k))
    (hS : (∑' k, (1-coldHistoryAlpha)*coldHistoryBeta^k*root k) ≤ S) :
    MemLp (fun ω => coldWeightedHistory coldHistoryAlpha (fun r => coldFiniteMaximum (X r) ω)) 20 ℙ ∧
    lpNorm (fun ω => coldWeightedHistory coldHistoryAlpha (fun r => coldFiniteMaximum (X r) ω)) 20 ℙ ≤
      coldTriangularHistoryCap M D a R S j := by
  let Z := fun r => coldFiniteMaximum (X r)
  let α := coldHistoryAlpha
  let β := coldHistoryBeta
  let κ := coldHistoryUnionFactor
  have hZm (r : ℕ) : MemLp (Z r) 20 ℙ := memLp_coldFiniteMaximum (hX r) (hMeas r)
  have hroot (k : ℕ) : 0 ≤ root k :=
    lpNorm_nonneg.trans (hfar k ⟨0,pow_pos (by norm_num) _⟩)
  have hfarZ (k : ℕ) : lpNorm (Z (k+j)) 20 ℙ ≤ κ^(k+j)*root k := by
    have h := coldFiniteMaximum_lpNorm_le (hX (k+j)) (hMeas (k+j)) (hroot k) (hfar k)
    have he : ((Fintype.card (Fin (9^(k+j)))):ℝ)^((1:ℝ)/20) = κ^(k+j) := by
      rw [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,cold_history_population_factor]
      exact (coldHistoryUnionFactor_pow _).symm
    rwa [he] at h
  have hnew (r : ℕ) (hr : r < j) : lpNorm (Z r) 20 ℙ ≤ coldHistoryDepthCap M D j r := by
    exact cold_history_depth_cap (by simp only [Fintype.card_fin]) (hX r) (hMeas r) (hn r)
      (hM _) (hraw r hr) (fun k _ => hD k)
      (fun k _ => coldCenteredMomentCap_nonneg (hM k) _) (hfluct r hr)
  have hcoarse (r : ℕ) (hr : r < j) : lpNorm (Z r) 20 ℙ ≤ κ^r*R := by
    have h := coldFiniteMaximum_lpNorm_le (hX r) (hMeas r) hR (fun i => (hraw r hr i).trans (hMR _))
    rw [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,cold_history_population_factor] at h
    simpa only [κ,coldHistoryUnionFactor_pow] using h
  let Eold := fun r => R*min 1 (4*Real.sqrt 19*(3:ℝ)^(-((j-r:ℕ):ℝ)))
  have hold (r : ℕ) (hr : r < j) : lpNorm (Z r) 20 ℙ ≤ a+κ^r*Eold r := by
    have hk0 : 0 ∈ coldHistoryEarlierLags j r := Finset.mem_range.mpr (Nat.succ_pos _)
    have hE : 0 ≤ Eold r := mul_nonneg hR (le_min (by norm_num) (by positivity))
    have hf (i : Fin (9^r)) : lpNorm (fun ω => max (X r i ω-a) 0) 20 ℙ ≤ Eold r := by
      have h := (cold_positive_threshold_mono (hX r i) hD0).trans (hfluct r hr 0 hk0 i)
      rw [hM0,Nat.sub_zero] at h
      exact h.trans (cold_root_centered_le_old hR (Nat.sub_pos_of_lt hr))
    have h := coldFiniteMaximum_centered_cap (hX r) (hMeas r) (hn r) ha hE hf
    rw [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,cold_history_population_factor] at h
    simpa only [κ,coldHistoryUnionFactor_pow] using h
  have hsplit := cold_complete_history_norm_split coldHistoryAlpha_pos.le coldHistoryAlpha_le_one
    coldHistoryBeta_pos.le cold_history_weight_relation hZm hStrong hS hnew hfarZ
  have hsplitR := cold_complete_history_norm_split coldHistoryAlpha_pos.le coldHistoryAlpha_le_one
    coldHistoryBeta_pos.le cold_history_weight_relation hZm hStrong hS hcoarse hfarZ
  have hsplitOld := cold_complete_history_norm_split coldHistoryAlpha_pos.le coldHistoryAlpha_le_one
    coldHistoryBeta_pos.le cold_history_weight_relation hZm hStrong hS hold hfarZ
  refine ⟨hsplit.1,le_min ?_ (le_min ?_ hsplit.2)⟩
  · have he : (∑ r ∈ Finset.range j, α^r*(κ^r*R)) = ∑ r ∈ Finset.range j, β^r*R := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← mul_assoc,← mul_pow,cold_history_weight_relation]
    rw [he] at hsplitR
    exact hsplitR.2.trans (cold_global_history_algebra coldHistoryBeta_pos.le hglobal j)
  · have he := cold_old_history_algebra α κ a S j Eold
    rw [cold_history_weight_relation] at he
    rw [he] at hsplitOld
    have he' : (1-α)*(∑ r ∈ Finset.range j, β^r*Eold r) =
        (1-α)*R*(∑ r ∈ Finset.range j, β^r*min 1 (4*Real.sqrt 19*(3:ℝ)^(-((j-r:ℕ):ℝ)))) := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      dsimp only [Eold]
      ring
    rw [he'] at hsplitOld
    exact hsplitOld.2

end ASDExplicitGamma.Cold
