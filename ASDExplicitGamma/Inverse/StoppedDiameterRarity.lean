module

public import ASDExplicitGamma.Inverse.StoppedClusterDiameter
public import ASDExplicitGamma.Inverse.StoppedPositiveMass

/-! The exact planar rare probability 26q for the actual diameter field. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- A summable probability envelope controls an actual countable event union. -/
theorem countable_union_probability_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : ℕ → Set Ω) (p : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p) (hE : ∀ n, μ.real (E n) ≤ p n) :
    μ.real (⋃ n, E n) ≤ ∑' n, p n := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (tsum_nonneg hp)).mp
  calc
    _ ≤ ∑' n, μ (E n) := measure_iUnion_le E
    _ ≤ ∑' n, ENNReal.ofReal (p n) := ENNReal.tsum_le_tsum fun n =>
      (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (hp n)).mpr (hE n)
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg hp hs).symm

/-- The unique aligned positive cube containing a site suffices to describe
all of that site's positive-label occupation. -/
theorem occupied_site_subset_labels {Ω : Type*} (B : PlanarMarks Ω) (x : BlockSite) :
    {ω | x ∈ markedOccupied B ω} ⊆ B.localMark x ∪
      ⋃ n, positiveActivation B n (alignedCubeIndex (3^(n+1)) x) := by
  rintro ω (hx | ⟨n,i,hi,hx⟩)
  · exact Or.inl hx
  · right
    apply Set.mem_iUnion.mpr
    have he := (aligned_cube_index_iff (3^(n+1)) (by positivity) x i).mpr hx
    exact ⟨n,by simpa only [he] using hi⟩

/-- An occupied site costs its local mark plus the complete positive-label
activation series, retaining each side-squared raw population. -/
theorem occupied_site_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (x : BlockSite) :
    μ.real {ω | x ∈ markedOccupied B ω} ≤ q+∑' n, positiveOccupancyCost n := by
  have hg := (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)).mul_left
    (9*Real.exp (-6120))
  have hs := hg.summable.of_nonneg_of_le (fun n => by unfold positiveOccupancyCost; positivity)
    positive_occupancy_majorant
  have hu := countable_union_probability_le μ
    (fun n => positiveActivation B n (alignedCubeIndex (3^(n+1)) x)) positiveOccupancyCost
    (fun n => by unfold positiveOccupancyCost; positivity) hs
    (fun n => control_activation_probability μ B q hB n _)
  calc
    _ ≤ μ.real (B.localMark x ∪ ⋃ n, positiveActivation B n (alignedCubeIndex (3^(n+1)) x)) :=
      measureReal_mono (occupied_site_subset_labels B x) (measure_ne_top μ _)
    _ ≤ μ.real (B.localMark x)+μ.real (⋃ n, positiveActivation B n (alignedCubeIndex (3^(n+1)) x)) :=
      measureReal_union_le _ _
    _ ≤ _ := add_le_add (hB.local_probability x) hu

theorem cluster_diameter_zero_of_not_occupied {Ω : Type*} (B : PlanarMarks Ω)
    (ω : Ω) (x : BlockSite) (hx : x ∉ markedOccupied B ω) :
    clusterDiameter B ω x = 0 := by
  classical
  apply le_antisymm _ zero_le
  apply iSup_le
  intro y
  apply iSup_le
  intro z
  have hp : ¬ (y ∈ clusterSites B ω x ∧ z ∈ clusterSites B ω x) := by
    rintro ⟨⟨hx',_,_⟩,_⟩
    exact hx hx'
  simp only [Set.indicator,Set.mem_ofPred_eq,hp,ite_false,le_refl]

/-- Positive source diameter requires an occupied component at one of exactly
25 roots; the extra one-q allowance pays every positive label together. -/
theorem diameter_field_rare_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hfloor : Real.exp (-6000) ≤ q) (x : BlockSite) :
    μ.real {ω | 0 < diameterField B ω x} ≤ 26*q := by
  have hsub : {ω | 0 < diameterField B ω x} ⊆
      ⋃ y ∈ diameterRoots x, {ω | y ∈ markedOccupied B ω} := by
    intro ω hω
    by_contra! hn
    have hb : diameterField B ω x ≤ 0 := by
      apply Finset.sup_le
      intro y hy
      have hnot : y ∉ markedOccupied B ω := fun hocc => hn (Set.mem_iUnion₂.mpr ⟨y,hy,hocc⟩)
      rw [cluster_diameter_zero_of_not_occupied B ω y hnot]
    exact not_lt_of_ge hb hω
  calc
    _ ≤ μ.real (⋃ y ∈ diameterRoots x, {ω | y ∈ markedOccupied B ω}) :=
      measureReal_mono hsub (measure_ne_top μ _)
    _ ≤ ∑ y ∈ diameterRoots x, μ.real {ω | y ∈ markedOccupied B ω} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _y ∈ diameterRoots x, (q+∑' n, positiveOccupancyCost n) :=
      Finset.sum_le_sum fun y _ => occupied_site_probability μ B q hB y
    _ = 25*q+25*(∑' n, positiveOccupancyCost n) := by
      rw [Finset.sum_const,nsmul_eq_mul,diameter_roots_card]
      norm_num only [Nat.cast_ofNat]
      ring
    _ ≤ 26*q := by linarith only [positive_occupancy_sum,hfloor]

end
end ASDExplicitGamma.Inverse
