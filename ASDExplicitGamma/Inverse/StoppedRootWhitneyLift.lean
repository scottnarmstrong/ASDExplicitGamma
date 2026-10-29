module

public import ASDExplicitGamma.Inverse.WhitneyRootLayerGeometry
public import ASDExplicitGamma.Inverse.StoppedWhitneyLift
public import ASDExplicitGamma.Inverse.StoppedRootFineSeparation
public import Algsuperdiff.Section3.Provider.Whitney.BoundaryDistance

/-! Actual Whitney lifts use at most two generations and the same extended
bad event. Their closure-touching steps remain fine-lattice steps. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- The source's actual ancestor at one fixed root depth, with only the two
allowed descendant generations. -/
def RootWhitneyLift (Q : TriadicCube 2) (h : ℕ) (V A : TriadicCube 2) : Prop :=
  A ∈ descendantsAtDepth Q h ∧
    ∃ r : ℕ, r ≤ 2 ∧ V ∈ descendantsAtDepth A r

/-- Every cube in the two adjacent layers has its genuine ancestor on the
coarser layer mesh; the generation mismatch is at most two. -/
theorem root_whitney_two_layer_lift (Q : TriadicCube 2) (H a n : ℕ)
    (han : a ≤ n) (hna : n ≤ a+1) {V : TriadicCube 2}
    (hV : V ∈ whitneyRootLayer Q H n) :
    ∃ A, RootWhitneyLift Q (a+whitneyProfile H a) V A := by
  have hvd := root_whitney_layer_descendants Q H n hV
  let base := a+whitneyProfile H a
  let depth := n+whitneyProfile H n
  have hmono := whitney_profile_mono H han
  have hstep := whitney_profile_step H a
  have hle : base ≤ depth := by dsimp only [base,depth]; omega
  have hgap : depth-base ≤ 2 := by
    dsimp only [base,depth]
    rcases (show n = a ∨ n = a+1 by omega) with rfl | rfl <;> omega
  have he : n+whitneyProfile H n = base+(depth-base) := by dsimp only [depth]; omega
  rw [he] at hvd
  obtain ⟨A,hA,hVA⟩ := exists_descendant_ancestor_at_depth base (depth-base) hvd
  exact ⟨A,hA,depth-base,hgap,hVA⟩

/-- A bad Whitney cell marks its ancestor's actual blocked q3 field, with
the ancestor label and the cell's own old-frame events kept exactly. -/
theorem root_whitney_lift_bad_occupied (M : ABKModel 2) (Q : TriadicCube 2) (h : ℕ)
    (τ η : ℝ) (ω : Algsuperdiff.Section3.Cutoff.CutoffSample 2)
    {V A : TriadicCube 2} (hVA : RootWhitneyLift Q h V A)
    (hbad : ω ∈ cellFailure M τ η V) :
    A.index ∈ fineOccupied (q3PlanarMarks M (Q.scale-h) τ η) ω := by
  have hs : A.scale = Q.scale-h := scale_eq_sub_of_mem_descendantsAtDepth hVA.1
  obtain ⟨r,hr,hV⟩ := hVA.2
  have hAe : (⟨Q.scale-h,A.index⟩ : TriadicCube 2) = A := by
    cases A with
    | mk scale index =>
      change scale = Q.scale-h at hs
      subst scale
      rfl
  change fineBlockIndex A.index ∈ markedOccupied _ ω
  exact q3_bad_descendant_occupied M (Q.scale-h) τ η A.index hr (by rw [hAe]; exact hV) ω hbad

/-- Closure-touching fine cells have equal or neighboring ancestor indices
on their common mesh, including all boundary touching points. -/
theorem root_whitney_lifts_touch_indices {Q : TriadicCube 2} {h : ℕ}
    {U V A B : TriadicCube 2} (hUA : RootWhitneyLift Q h U A)
    (hVB : RootWhitneyLift Q h V B) (ht : Whitney.CubeTouch U V) :
    ∀ d, |B.index d-A.index d| ≤ 1 := by
  obtain ⟨z,hzU,hzV⟩ := ht
  obtain ⟨r,hr,hU⟩ := hUA.2
  obtain ⟨s,hs,hV⟩ := hVB.2
  have htAB : Whitney.CubeTouch A B :=
    ⟨z,descendant_closed_cube_subset hU hzU,descendant_closed_cube_subset hV hzV⟩
  have hAs : A.scale = Q.scale-h := scale_eq_sub_of_mem_descendantsAtDepth hUA.1
  have hBs : B.scale = Q.scale-h := scale_eq_sub_of_mem_descendantsAtDepth hVB.1
  have hpos : (0:ℝ) < (3:ℝ)^(Q.scale-(h:ℤ)) := zpow_pos (by norm_num) _
  intro d
  have hd := Whitney.cubeTouch_iff.mp htAB d
  rw [cubeRadius_eq_zpow_div_two,cubeRadius_eq_zpow_div_two,hAs,hBs] at hd
  simp only [cubeCenter,cubeScaleFactor,hAs,hBs] at hd
  have hreal : |(B.index d:ℝ)-(A.index d:ℝ)| ≤ 1 := by
    rw [show (A.index d:ℝ)*(3:ℝ)^(Q.scale-(h:ℤ))-(B.index d:ℝ)*(3:ℝ)^(Q.scale-(h:ℤ)) =
      ((A.index d:ℝ)-(B.index d:ℝ))*(3:ℝ)^(Q.scale-(h:ℤ)) by ring,
      abs_mul,abs_of_pos hpos] at hd
    rw [abs_sub_comm]
    nlinarith only [hd,hpos]
  exact_mod_cast hreal

end
end ASDExplicitGamma.Inverse
