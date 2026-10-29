module

public import ASDExplicitGamma.Inverse.StoppedHeightTail
public import ASDExplicitGamma.Inverse.StoppedFiniteClusters

/-! The selected source height is almost surely a genuine successful separation cutoff. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory Filter
noncomputable section

/-- The exceptional samples with failed separations arbitrarily far above the
entrance have probability zero, proved from the full future-height bound. -/
theorem height_unsuccessful_null {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H0 : ℕ) (hH0 : 333 ≤ H0) (E : ℕ → Set Ω)
    (hE : ∀ k, H0 ≤ k → μ.real (E k) ≤ Real.exp (-heightExponent k/12)) :
    μ {ω | ¬ HeightSuccessful H0 E ω} = 0 := by
  have hsub (n : ℕ) : {ω | ¬ HeightSuccessful H0 E ω} ⊆
      ⋃ k : ℕ, ⋃ _hk : H0+n ≤ k, E k := by
    intro ω hω
    by_contra hn
    have hall : ∀ k, H0+n ≤ k → ω ∉ E k := by
      intro k hk hmem
      exact hn (Set.mem_iUnion.mpr ⟨k,Set.mem_iUnion.mpr ⟨hk,hmem⟩⟩)
    exact hω ⟨H0+n,⟨by omega,hall⟩⟩
  have hb (n : ℕ) : μ.real {ω | ¬ HeightSuccessful H0 E ω} ≤ Real.exp (-(n:ℝ)/2) := by
    have hh := future_failure_probability μ E (H0+n) (by omega)
      (fun k hk => hE k (by omega))
    apply ((measureReal_mono (μ := μ) (hsub n) (measure_ne_top μ _)).trans hh).trans
    apply Real.exp_le_exp.mpr
    have hp := height_linear_payment (H0+n) (by omega)
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have h00 : (0:ℝ) ≤ H0 := Nat.cast_nonneg _
    push_cast at hp
    linarith only [hp,hn,h00]
  have hz := ge_of_tendsto radius_majorant_tendsto_zero (Eventually.of_forall hb)
  exact (measureReal_eq_zero_iff (by finiteness)).mp (le_antisymm hz measureReal_nonneg)

/-- Every separation at and above the actual selected height succeeds almost
surely, with the literal source entrance retained. -/
theorem stopped_height_ae_good {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H0 : ℕ) (hH0 : 333 ≤ H0) (E : ℕ → Set Ω)
    (hE : ∀ k, H0 ≤ k → μ.real (E k) ≤ Real.exp (-heightExponent k/12)) :
    ∀ᵐ ω ∂μ, HeightGood H0 E ω (stoppedHeight H0 E ω) := by
  have hs : ∀ᵐ ω ∂μ, HeightSuccessful H0 E ω :=
    ae_iff.mpr (height_unsuccessful_null μ H0 hH0 E hE)
  filter_upwards [hs] with ω hω
  exact stopped_height_good H0 E ω hω

end
end ASDExplicitGamma.Inverse
