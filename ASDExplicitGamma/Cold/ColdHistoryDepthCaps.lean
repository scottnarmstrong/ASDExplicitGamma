module

public import ASDExplicitGamma.Cold.TraceMaximumCaps
public import ASDExplicitGamma.Cold.ColdMomentCaps

/-! # The strictly triangular source depth-cap candidates -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Available earlier-lag candidates at one source depth. The current lag k=j is excluded. -/
def coldHistoryEarlierLags (j r : ℕ) : Finset ℕ := Finset.range (min (j-r) (j-1)+1)

/-- There is always the certified root-lag candidate. -/
theorem coldHistoryEarlierLags_nonempty (j r : ℕ) : (coldHistoryEarlierLags j r).Nonempty := by
  exact Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _)

/-- The exact `C_(j,r)` from the corrected source formula. -/
def coldHistoryDepthCap (M D : ℕ → ℝ) (j r : ℕ) : ℝ :=
  min ((9:ℝ)^((r:ℝ)/20)*M (j-r))
    ((coldHistoryEarlierLags j r).inf' (coldHistoryEarlierLags_nonempty j r)
      (fun k => D k+(9:ℝ)^((r:ℝ)/20)*coldCenteredMomentCap (M k) (j-r-k)))

/-- Every available candidate uses only an earlier completed lag. -/
theorem coldHistoryEarlierLags_lt {j r k : ℕ} (hj : 0 < j)
    (hk : k ∈ coldHistoryEarlierLags j r) : k < j := by
  have h := Finset.mem_range.mp hk
  dsimp only [coldHistoryEarlierLags] at hk
  omega

/-- The spatial population factor is exactly the source `9^(r/20)`. -/
theorem cold_history_population_factor (r : ℕ) :
    ((9:ℝ)^r)^((1:ℝ)/20) = (9:ℝ)^((r:ℝ)/20) := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 9)]
  congr 1
  ring

/-- Assemble the actual raw and positive-fluctuation maximum candidates into C_(j,r).
Only per-cell moment/fluctuation caps are inputs; no bound on a maximum is assumed. -/
theorem cold_history_depth_cap {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] [Fintype ι] [Nonempty ι] {X : ι → Ω → ℝ}
    {M D : ℕ → ℝ} {j r : ℕ} (hcard : Fintype.card ι = 9^r)
    (hX : ∀ i, MemLp (X i) 20 ℙ) (hMeas : ∀ i, Measurable (X i))
    (hn : ∀ i, ∀ᵐ ω ∂ℙ, 0 ≤ X i ω)
    (hM : 0 ≤ M (j-r)) (hraw : ∀ i, lpNorm (X i) 20 ℙ ≤ M (j-r))
    (hD : ∀ k ∈ coldHistoryEarlierLags j r, 0 ≤ D k)
    (hE : ∀ k ∈ coldHistoryEarlierLags j r, 0 ≤ coldCenteredMomentCap (M k) (j-r-k))
    (hfluct : ∀ k ∈ coldHistoryEarlierLags j r, ∀ i,
      lpNorm (fun ω => max (X i ω-D k) 0) 20 ℙ ≤ coldCenteredMomentCap (M k) (j-r-k)) :
    lpNorm (coldFiniteMaximum X) 20 ℙ ≤ coldHistoryDepthCap M D j r := by
  have hpop : (Fintype.card ι:ℝ)^((1:ℝ)/20) = (9:ℝ)^((r:ℝ)/20) := by
    rw [hcard,Nat.cast_pow,Nat.cast_ofNat,cold_history_population_factor]
  apply le_min
  · have h := coldFiniteMaximum_lpNorm_le hX hMeas hM hraw
    rwa [hpop] at h
  · apply Finset.le_inf' (coldHistoryEarlierLags_nonempty j r)
    intro k hk
    have h := coldFiniteMaximum_centered_cap hX hMeas hn (hD k hk) (hE k hk) (hfluct k hk)
    rwa [hpop] at h

end ASDExplicitGamma.Cold
