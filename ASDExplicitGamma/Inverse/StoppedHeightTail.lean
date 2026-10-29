module

public import ASDExplicitGamma.Inverse.StoppedHeightSelection
public import ASDExplicitGamma.Inverse.StoppedHeightPayments
public import ASDExplicitGamma.Inverse.StoppedRouteLimit

/-! The complete infinite failure union yields the exact stopped-height tail. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped BigOperators
noncomputable section

/-- The actual supergeometric height profile is summable, derived without a
summability premise or a finite truncation of its future failures. -/
theorem height_tail_summable (h : ℕ) (hh : 333 ≤ h) :
    Summable (fun n : ℕ => Real.exp (-heightExponent (h+n)/12)) := by
  have hl (n : ℕ) : (n:ℝ) ≤ heightExponent (h+n)/12 := by
    have hp := height_linear_payment (h+n) (by omega)
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have hh0 : (0:ℝ) ≤ h := Nat.cast_nonneg _
    push_cast at hp
    linarith only [hp,hn,hh0]
  simpa only [neg_one_mul,neg_div] using
    Real.summable_exp_nat_mul_of_ge (by norm_num : (-1:ℝ) < 0) hl

/-- Every complete future failure union has the exact source tail. No
independence between heights is needed. -/
theorem future_failure_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : ℕ → Set Ω) (h : ℕ) (hh : 333 ≤ h)
    (hE : ∀ k, h ≤ k → μ.real (E k) ≤ Real.exp (-heightExponent k/12)) :
    μ.real (⋃ k : ℕ, ⋃ _hk : h ≤ k, E k) ≤ Real.exp (-heightExponent h/32) := by
  let F (N : ℕ) : Set Ω := ⋃ n ∈ Finset.range N, E (h+n)
  have hmono : Monotone F := by
    intro N M hNM ω hω
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hω
    obtain ⟨hn,hω⟩ := Set.mem_iUnion.mp hn
    exact Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨Finset.range_mono hNM hn,hω⟩⟩
  have hb (N : ℕ) : μ.real (F N) ≤ Real.exp (-heightExponent h/32) := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, μ.real (E (h+n)) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ n ∈ Finset.range N, Real.exp (-heightExponent (h+n)/12) :=
        Finset.sum_le_sum (fun n _ => hE (h+n) (by omega))
      _ ≤ ∑' n : ℕ, Real.exp (-heightExponent (h+n)/12) :=
        (height_tail_summable h hh).sum_le_tsum _ (fun n _ => (Real.exp_pos _).le)
      _ ≤ _ := stopped_height_probability_series h hh
  have hall := increasing_event_bound μ F hmono _ (Real.exp_pos _).le hb
  have he : (⋃ k : ℕ, ⋃ _hk : h ≤ k, E k) = ⋃ N : ℕ, F N := by
    ext ω
    constructor
    · intro hω
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hω
      obtain ⟨hkh,hω⟩ := Set.mem_iUnion.mp hk
      refine Set.mem_iUnion.mpr ⟨k-h+1,Set.mem_iUnion.mpr ⟨k-h,?_⟩⟩
      exact Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),by simpa only [Nat.add_sub_of_le hkh] using hω⟩
    · intro hω
      obtain ⟨N,hω⟩ := Set.mem_iUnion.mp hω
      obtain ⟨n,hω⟩ := Set.mem_iUnion.mp hω
      obtain ⟨_,hω⟩ := Set.mem_iUnion.mp hω
      exact Set.mem_iUnion.mpr ⟨h+n,Set.mem_iUnion.mpr ⟨by omega,hω⟩⟩
  rw [he]
  exact hall

/-- The source height tail at either entrance, from the actual full failure
sequence. Its probability bound does not assume any height measurability. -/
theorem stopped_height_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H0 : ℕ) (hH0 : 333 ≤ H0) (E : ℕ → Set Ω)
    (hE : ∀ k, H0 ≤ k → μ.real (E k) ≤ Real.exp (-heightExponent k/12))
    (h : ℕ) (hh : H0 ≤ h) :
    μ.real {ω | h < stoppedHeight H0 E ω} ≤ Real.exp (-heightExponent h/32) :=
  (measureReal_mono (μ := μ) (stopped_height_tail_subset H0 E h hh) (measure_ne_top μ _)).trans
    (future_failure_probability μ E h (hH0.trans hh) (fun k hk => hE k (hh.trans hk)))

end
end ASDExplicitGamma.Inverse
