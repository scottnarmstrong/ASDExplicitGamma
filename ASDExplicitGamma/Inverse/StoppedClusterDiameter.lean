module

public import ASDExplicitGamma.Inverse.StoppedClusterMembership

/-! The source component diameter and radius-two neighborhood field, before localization. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The exact integer infinity distance of two physical block sites. -/
def blockDistance (x y : BlockSite) : ℕ :=
  max (y 0-x 0).natAbs (y 1-x 1).natAbs

/-- Actual component diameter plus one, zero on empty components. The extended
carrier also gives the literal supremum on exceptional unbounded components. -/
def clusterDiameter {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω) (x : BlockSite) : ℝ≥0∞ :=
  ⨆ y : BlockSite, ⨆ z : BlockSite,
    ({ω | y ∈ clusterSites B ω x ∧ z ∈ clusterSites B ω x}).indicator
      (fun _ => ((blockDistance y z+1:ℕ):ℝ≥0∞)) ω

/-- Exactly the 25 possible roots in the source radius-two block neighborhood. -/
def diameterRoots (x : BlockSite) : Finset BlockSite :=
  blockCubeSites (fun d => x d-2) 5

theorem diameter_roots_card (x : BlockSite) : (diameterRoots x).card = 25 := by
  rw [diameterRoots,block_cube_sites_card]
  norm_num

/-- The literal source field Z: largest component diameter plus one among
all components meeting the radius-two neighborhood of the current block. -/
def diameterField {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω) (x : BlockSite) : ℝ≥0∞ :=
  (diameterRoots x).sup (fun y => clusterDiameter B ω y)

theorem cluster_diameter_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (x : BlockSite) :
    Measurable (fun ω => clusterDiameter B ω x) := by
  apply Measurable.iSup
  intro y
  apply Measurable.iSup
  intro z
  exact measurable_const.indicator ((cluster_sites_mem_measurable B hL hP x y).inter
    (cluster_sites_mem_measurable B hL hP x z))

/-- Finiteness follows from the actual finite component, not a diameter bound
included as a new probabilistic premise. -/
theorem cluster_diameter_ne_top_of_finite {Ω : Type*} (B : PlanarMarks Ω)
    (ω : Ω) (x : BlockSite) (hx : (clusterSites B ω x).Finite) :
    clusterDiameter B ω x ≠ ∞ := by
  classical
  obtain ⟨N,hN⟩ := ((hx.prod hx).image (fun p : BlockSite × BlockSite => blockDistance p.1 p.2+1)).bddAbove
  have hb : clusterDiameter B ω x ≤ (N:ℝ≥0∞) := by
    apply iSup_le
    intro y
    apply iSup_le
    intro z
    by_cases hp : y ∈ clusterSites B ω x ∧ z ∈ clusterSites B ω x
    · simp only [Set.indicator,Set.mem_ofPred_eq,hp.1,hp.2,true_and,ite_true]
      have hpair : (y,z) ∈ clusterSites B ω x ×ˢ clusterSites B ω x := ⟨hp.1,hp.2⟩
      have hn : blockDistance y z+1 ≤ N := hN (Set.mem_image_of_mem _ hpair)
      exact_mod_cast hn
    · simp only [Set.indicator,Set.mem_ofPred_eq,hp,ite_false]
      exact zero_le
  exact ne_of_lt (hb.trans_lt (by finiteness))

/-- The finite-neighborhood maximum is a measurable random diameter field. -/
theorem diameter_field_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : PlanarMarks Ω) (hL : ∀ x, MeasurableSet (B.localMark x))
    (hP : ∀ n x, MeasurableSet (B.positiveMark n x)) (x : BlockSite) :
    Measurable (fun ω => diameterField B ω x) := by
  have hm (s : Finset BlockSite) : Measurable (fun ω => s.sup (fun y => clusterDiameter B ω y)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sup_empty] using measurable_const (a := (⊥:ℝ≥0∞))
    | @insert y s hy ih =>
      simpa only [Finset.sup_insert] using (cluster_diameter_measurable B hL hP y).max ih
  exact hm (diameterRoots x)

/-- The literal field Z is finite almost surely, simultaneously at all blocks. -/
theorem diameter_field_ae_ne_top {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) :
    ∀ᵐ ω ∂μ, ∀ x : BlockSite, diameterField B ω x ≠ ∞ := by
  filter_upwards [clusters_ae_finite μ B q hB hq0 hq] with ω hω
  intro x
  change (diameterRoots x).sup (fun y => clusterDiameter B ω y) ≠ ⊤
  intro htop
  obtain ⟨y,_,hy⟩ := Finset.sup_eq_top_iff.mp htop
  exact cluster_diameter_ne_top_of_finite B ω y (hω y) hy

end
end ASDExplicitGamma.Inverse
