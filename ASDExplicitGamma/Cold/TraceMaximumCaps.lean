module

public import ASDExplicitGamma.Cold.FiniteTraceMaximum

/-! # Raw and centered candidates for a depthwise trace maximum -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- The deterministic mean cap stays outside the spatial maximum. -/
theorem coldFiniteMaximum_le_mean_add_positive {Ω ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → Ω → ℝ) (D : ℝ) (ω : Ω) :
    coldFiniteMaximum X ω ≤ D+coldFiniteMaximum (fun i ω => max (X i ω-D) 0) ω := by
  obtain ⟨i,hi⟩ := coldFiniteMaximum_eq_some X ω
  rw [hi]
  have h := le_coldFiniteMaximum (fun i ω => max (X i ω-D) 0) ω i
  have hp := le_max_left (X i ω-D) 0
  linarith only [h,hp]

/-- The source `D+N^(1/20)*E` maximum candidate, with no independence between cells. -/
theorem coldFiniteMaximum_centered_cap {Ω ι : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] [Fintype ι] [Nonempty ι] {X : ι → Ω → ℝ} {D E : ℝ}
    (hX : ∀ i, MemLp (X i) 20 ℙ) (hMeas : ∀ i, Measurable (X i))
    (hn : ∀ i, ∀ᵐ ω ∂ℙ, 0 ≤ X i ω) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hcap : ∀ i, lpNorm (fun ω => max (X i ω-D) 0) 20 ℙ ≤ E) :
    lpNorm (coldFiniteMaximum X) 20 ℙ ≤ D+(Fintype.card ι:ℝ)^((1:ℝ)/20)*E := by
  let Y := fun i ω => max (X i ω-D) 0
  have hY (i : ι) : MemLp (Y i) 20 ℙ := ((hX i).sub (memLp_const D)).pos_part
  have hYm (i : ι) : Measurable (Y i) := (hMeas i |>.sub measurable_const).max measurable_const
  have hmax := memLp_coldFiniteMaximum hY hYm
  have hM : MemLp (fun ω => D+coldFiniteMaximum Y ω) 20 ℙ := (memLp_const D).add hmax
  have hnmax : ∀ᵐ ω ∂ℙ, 0 ≤ coldFiniteMaximum X ω := by
    filter_upwards [ae_all_iff.mpr hn] with ω hω
    obtain ⟨i,he⟩ := coldFiniteMaximum_eq_some X ω
    rw [he]
    exact hω i
  have hymax (ω : Ω) : 0 ≤ coldFiniteMaximum Y ω := by
    obtain ⟨i,he⟩ := coldFiniteMaximum_eq_some Y ω
    rw [he]
    exact le_max_right _ _
  have hmono := cold_lpNorm_mono_ae hM (show ∀ᵐ ω ∂ℙ,
      ‖coldFiniteMaximum X ω‖ ≤ ‖D+coldFiniteMaximum Y ω‖ from by
    filter_upwards [hnmax] with ω hnω
    rw [Real.norm_eq_abs,abs_of_nonneg hnω,Real.norm_eq_abs,abs_of_nonneg (add_nonneg hD (hymax ω))]
    exact coldFiniteMaximum_le_mean_add_positive X D ω)
  have ht := lpNorm_add_le (memLp_const (μ := ℙ) D) (g := coldFiniteMaximum Y) (by norm_num : (1:ℝ≥0∞) ≤ 20)
  have hfun : (fun ω => D+coldFiniteMaximum Y ω) = (fun _ => D)+coldFiniteMaximum Y := rfl
  rw [hfun] at hmono
  have hc : lpNorm (fun _ : Ω => D) 20 ℙ = D := by
    rw [lpNorm_const' (by norm_num : (20:ℝ≥0∞) ≠ 0) (by norm_num : (20:ℝ≥0∞) ≠ ⊤)]
    simp only [Real.norm_eq_abs,abs_of_nonneg hD,probReal_univ,Real.one_rpow,mul_one]
  rw [hc] at ht
  exact hmono.trans (ht.trans (add_le_add (le_refl _)
    (coldFiniteMaximum_lpNorm_le hY hYm hE hcap)))

end ASDExplicitGamma.Cold
