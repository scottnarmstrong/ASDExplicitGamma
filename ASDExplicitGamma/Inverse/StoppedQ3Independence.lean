module

public import ASDExplicitGamma.Inverse.StoppedQ3Locality
public import ASDExplicitGamma.Inverse.StoppedMarkControl
public import ASDExplicitGamma.Inverse.RestrictionLocalSigma

/-! Independence of the literal q3 mark families from the cold theorem. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model
noncomputable section

/-- Every same-parity local population is independent as a family of actual
completed cutoff observables, including all descendant histories. -/
theorem q3_local_marks_independent {I : Type} [Fintype I]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (j : ℤ) (τ η : ℝ)
    (x : I → BlockSite) (hx : Pairwise fun i k => ∃ d, 1 < |x k d-x i d|) :
    iIndepFun (fun i => markIndicator ((q3PlanarMarks M j τ η).localMark (x i)))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply restriction_local_observables_independent M h hM (j+40)
    (fun i => physicalBlockRegion j (x i) 1)
    (fun i => physical_block_region_measurable j (x i) 1)
  · intro i k hik p hp r hr
    have hg : ∃ d, 2*(1:ℤ) ≤ |x k d-x i d| := by
      obtain ⟨d,hd⟩ := hx hik
      exact ⟨d,by omega⟩
    obtain ⟨d,hd⟩ := physical_block_region_gap j (x i) (x k) 1 hg hp hr
    refine ⟨d,?_⟩
    have hz : 0 ≤ (3:ℝ)^(j+40) := (zpow_pos (by norm_num) _).le
    simp only [physicalBlockSide,Nat.cast_one,mul_one] at hd
    linarith only [hd,hz]
  · intro i
    let localInfo : MeasurableSpace (Cutoff.CutoffSample 2) :=
      Cutoff.cutoffSampleLocalSigma M (j+40) (physicalBlockRegion j (x i) 1)
    exact mark_indicator_measurable _ (q3_local_mark_local M j τ η (x i))

/-- Complete observation carrier for an activated positive cube, as a union
of its actual elementary physical blocks. -/
def physicalActivationRegion (j : ℤ) (n : ℕ) (i : BlockSite) : Set (Vec 2) :=
  ⋃ x ∈ blockCubeSites (alignedCubeBase (3^(n+1)) i) (3^(n+1)),
    physicalBlockRegion j x 1

theorem physical_activation_region_measurable (j : ℤ) (n : ℕ) (i : BlockSite) :
    MeasurableSet (physicalActivationRegion j n i) := by
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro _
  exact physical_block_region_measurable j x 1

/-- A one-block carrier fits in any larger side-s carrier at the same base. -/
theorem physical_block_region_mono_side (j : ℤ) (x : BlockSite) {s t : ℕ} (hst : s ≤ t) :
    physicalBlockRegion j x s ⊆ physicalBlockRegion j x t := by
  intro p hp d
  refine ⟨(hp d).1, (hp d).2.trans ?_⟩
  have hc : (s:ℝ) ≤ t := by exact_mod_cast hst
  have hm := mul_le_mul_of_nonneg_left hc (physical_block_side_pos j).le
  linarith only [hm]

/-- Same-color activation cubes retain a full fresh-shell coordinate gap
between every pair of points of their complete observation carriers. -/
theorem physical_activation_region_gap (j : ℤ) (n : ℕ) (i k : BlockSite)
    (hik : i ≠ k) (hc : blockColor i = blockColor k)
    {p r : Vec 2} (hp : p ∈ physicalActivationRegion j n i)
    (hr : r ∈ physicalActivationRegion j n k) :
    ∃ d, (3:ℝ)^(j+40+(n+1)) ≤ |(p-r) d| := by
  obtain ⟨x,hx,hp⟩ := Set.mem_iUnion₂.mp hp
  obtain ⟨y,hy,hr⟩ := Set.mem_iUnion₂.mp hr
  have hs : 0 < 3^(n+1) := by positivity
  have hg := same_color_cube_sites_separated (3^(n+1)) hs i k hik
    ((block_color_eq_iff i k).mp hc) x y
    ((mem_cube_sites _ _ _).mp hx) ((mem_cube_sites _ _ _).mp hy)
  have hg' : ∃ d, 2*((3^(n+1):ℕ):ℤ) ≤ |y d-x d| := by
    obtain ⟨d,hd⟩ := hg
    exact ⟨d,hd.le⟩
  obtain ⟨d,hd⟩ := physical_block_region_gap j x y (3^(n+1)) hg'
    (physical_block_region_mono_side j x hs hp)
    (physical_block_region_mono_side j y hs hr)
  refine ⟨d,?_⟩
  have he : (3:ℝ)^(j+40+(n+1)) = (3:ℝ)^(j+40)*(3:ℝ)^(n+1:ℕ) := by
    rw [zpow_add₀ (by norm_num : (3:ℝ) ≠ 0)]
    rw [show (n:ℤ)+1 = ((n+1:ℕ):ℤ) by omega,zpow_natCast]
  rw [he]
  simp only [physicalBlockSide,Nat.cast_pow,Nat.cast_ofNat] at hd
  have hz : 0 ≤ (3:ℝ)^(j+40)*(3:ℝ)^(n+1) := by positivity
  nlinarith only [hd,hz]

/-- An activated cube reads its entire finite family of marks in the union
of their physical restriction carriers. -/
theorem q3_positive_activation_local (M : ABKModel 2) (j : ℤ) (τ η : ℝ)
    (n : ℕ) (i : BlockSite) :
    MeasurableSet[Cutoff.cutoffSampleLocalSigma M (j+40+(n+1)) (physicalActivationRegion j n i)]
      (positiveActivation (q3PlanarMarks M j τ η) n i) := by
  let activationInfo : MeasurableSpace (Cutoff.CutoffSample 2) :=
    Cutoff.cutoffSampleLocalSigma M (j+40+(n+1)) (physicalActivationRegion j n i)
  apply MeasurableSet.iUnion
  intro x
  apply MeasurableSet.iUnion
  intro hx
  have hU : physicalBlockRegion j x 1 ⊆ physicalActivationRegion j n i := by
    intro p hp
    exact Set.mem_iUnion₂.mpr ⟨x,hx,hp⟩
  exact (Algsuperdiff.Section3.Provider.BadEvents.cutoffSampleLocalSigma_mono M le_rfl hU) _
    (q3_positive_mark_local M j τ η n x)

/-- All same-color activation events are jointly independent, obtained from
the completed cutoff sigma-fields rather than pairwise event independence. -/
theorem q3_positive_activations_independent {I : Type} [Fintype I]
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (j : ℤ) (τ η : ℝ)
    (n : ℕ) (x : I → BlockSite) (c : Fin 9) (hx : Function.Injective x)
    (hc : ∀ i, blockColor (x i) = c) :
    iIndepFun (fun i => markIndicator (positiveActivation (q3PlanarMarks M j τ η) n (x i)))
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply restriction_local_observables_independent M h hM (j+40+(n+1))
    (fun i => physicalActivationRegion j n (x i))
    (fun i => physical_activation_region_measurable j n (x i))
  · intro i k hik p hp r hr
    exact physical_activation_region_gap j n (x i) (x k) (fun he => hik (hx he))
      ((hc i).trans (hc k).symm) hp hr
  · intro i
    let activationInfo : MeasurableSpace (Cutoff.CutoffSample 2) :=
      Cutoff.cutoffSampleLocalSigma M (j+40+(n+1)) (physicalActivationRegion j n (x i))
    exact mark_indicator_measurable _ (q3_positive_activation_local M j τ η n (x i))

end
end ASDExplicitGamma.Inverse
