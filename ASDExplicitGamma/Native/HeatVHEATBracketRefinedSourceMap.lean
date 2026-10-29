module

public import ASDExplicitGamma.Native.HeatVHEATBracketRefinedParentLaw
public import Algsuperdiff.Section3.Provider.Whitney.BoundaryDistance
import ASDExplicitGamma.Gaussian.Q3RemainderCameronMartin
import ASDExplicitGamma.Main.CubeFactor

/-! The common parent q3 source, after centering on each actual refined child,
is the same white-noise source as the child q3 remainder factor. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Set

local instance nativeHeatQ3RefinedDomainCompact_sourceMap (m : ℤ) :
    CompactSpace (nativeHeatQ3RefinedCarrierDomain m) := by
  apply isCompact_iff_compactSpace.mp
  apply isCompact_iUnion
  intro i
  exact (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

def nativeHeatQ3RefinedCarrierChildRectangle
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) : Set (Vec 2) :=
  closedRectangle
    (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
    (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
      cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
    (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
    (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
      cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))

local instance nativeHeatQ3RefinedRectangleCompact_sourceMap (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (nativeHeatQ3RefinedCarrierChildRectangle m i) := by
  unfold nativeHeatQ3RefinedCarrierChildRectangle
  infer_instance

theorem nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) :
    closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)) ⊆
      nativeHeatQ3RefinedCarrierChildRectangle m i := by
  let Q := nativeHeatQ3RefinedCarrierChild m i
  let R := nativeHeatQ3RefinedCarrierChildRectangle m i
  have hbox : cubeSet Q =
      Set.pi Set.univ (fun a : Fin 2 => Set.Ico (cubeCorner Q a)
        (cubeCorner Q a + cubeScaleFactor Q)) :=
    Triadic.cubeSet_eq_box Q
  have hsub : cubeSet Q ⊆ R := by
    rw [hbox]
    intro y hy
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ico] at hy
    change y 0 ∈ Set.Icc (cubeCorner Q 0) (cubeCorner Q 0 + cubeScaleFactor Q) ∧
      y 1 ∈ Set.Icc (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q)
    exact ⟨⟨(hy 0).1, le_of_lt (hy 0).2⟩,
      ⟨(hy 1).1, le_of_lt (hy 1).2⟩⟩
  have hclosed : IsClosed R := by
    change IsClosed {y : Vec 2 | y 0 ∈ Set.Icc (cubeCorner Q 0)
      (cubeCorner Q 0 + cubeScaleFactor Q) ∧
      y 1 ∈ Set.Icc (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q)}
    exact (isClosed_Icc.preimage (continuous_apply 0)).inter
      (isClosed_Icc.preimage (continuous_apply 1))
  exact closure_minimal hsub hclosed

noncomputable def nativeHeatQ3RefinedCarrierChildRectangleToCube
    (m : ℤ) (i : nativeHeatQ3RefinedCarrierIndex) :
    C(nativeHeatQ3RefinedCarrierChildRectangle m i, ℝ) →L[ℝ]
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ) := by
  let e : closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)) →
      nativeHeatQ3RefinedCarrierChildRectangle m i :=
    fun x => ⟨x.1, nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i x.2⟩
  exact ContinuousMap.compCLM ℝ ℝ ⟨e, continuous_subtype_val.subtype_mk _⟩

/-- The parent field restricted to the refined carrier and centered separately
on each child agrees, for the same white-noise input, with the actual physical
q3 remainder factor on each child. -/
theorem nativeHeatQ3RefinedCarrierParentCenteredSource_eq_childRemainders
    (M : ABKModel 2) (h : ℝ) (m : ℤ) (d : Fin 9)
    (u : WhiteNoise) :
    let s : ℕ := d.val + 2
    let β := q3ModelAmplitude M h (m + (s : ℤ))
    let L := q3ModelLength (m + (s : ℤ))
    let U : nativeHeatQ3RefinedCarrierIndex → Set (Vec 2) :=
      fun i => closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    let hU : ∀ i, U i ⊆ nativeHeatQ3RefinedCarrierDomain m :=
      nativeHeatQ3RefinedCarrierChild_closure_subset m
    let centers := nativeHeatQ3RefinedCarrierCenter m
    let old := nativeHeatQ3RefinedCarrierParentRestrict m
    let parent := mainCubeH3Value (m + 10) β L
      ∘L q3H3RangeFactor (-mainCubeHalfSide (m + 10))
        (mainCubeHalfSide (m + 10)) (-mainCubeHalfSide (m + 10))
        (mainCubeHalfSide (m + 10)) β L
    childRemainderMap U hU centers (old (parent u)) =
      fun i => nativeHeatQ3RefinedCarrierChildRectangleToCube m i
        (q3RemainderValueFactor
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          β L
          ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
            nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
              (subset_closure (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet
                (nativeHeatQ3RefinedCarrierChild m i)))⟩ u) := by
  classical
  intro s β L U hU centers old parent
  apply funext
  intro i
  apply ContinuousMap.ext
  intro x
  let hxrect : ↥(nativeHeatQ3RefinedCarrierChildRectangle m i) :=
    ⟨x.1, nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i x.2⟩
  let hxparent : ↥(closure (cubeSet (originCube 2 (m + 10)))) :=
    ⟨x.1, nativeHeatQ3RefinedCarrierDomain_subset_parent m (hU i x.2)⟩
  let hcenterParent : ↥(closure (cubeSet (originCube 2 (m + 10)))) :=
    ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
        nativeHeatQ3RefinedCarrierDomain_subset_parent m
          ((nativeHeatQ3RefinedCarrierCenter m i).2)⟩
  have hparentValue (y : closure (cubeSet (originCube 2 (m + 10)))) :
      mainCubeH3Value (m + 10) β L
        (q3H3RangeFactor (-mainCubeHalfSide (m + 10))
          (mainCubeHalfSide (m + 10)) (-mainCubeHalfSide (m + 10))
          (mainCubeHalfSide (m + 10)) β L u) y =
        q3Convolution β L h3Zero u y.1 := by
    exact mainCubeH3Value_factor (m + 10) β L u y
  have hchildValue (y : ↥(nativeHeatQ3RefinedCarrierChildRectangle m i)) :
      q3RemainderValueFactor
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
          cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
          cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i)) β L
        ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
          nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
            (subset_closure (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet
              (nativeHeatQ3RefinedCarrierChild m i)))⟩ u y =
      q3Convolution β L h3Zero u y.1 -
        q3Convolution β L h3Zero u
          (cubeCenter (nativeHeatQ3RefinedCarrierChild m i)) := by
    have hside : 0 < cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i) := by
      unfold cubeScaleFactor
      positivity
    have hab : cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 <
        cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
          cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i) := by
      linarith
    have hcd : cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 <
        cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
          cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i) := by
      linarith
    let c : ↥(nativeHeatQ3RefinedCarrierChildRectangle m i) :=
      ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
          nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
            (subset_closure (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet
              (nativeHeatQ3RefinedCarrierChild m i)))⟩
    change centeringMap c
      (q3H3RangeValue
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
          cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
          cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i)) β L
        (q3H3RangeFactor
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i)) β L u)) y = _
    calc
      _ = q3H3RangeValue
            (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
            (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
              cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
            (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
            (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
              cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i)) β L
            (q3H3RangeFactor
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
                cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
                cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i)) β L u) y -
          q3H3RangeValue
            (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
            (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
              cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
            (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
            (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
              cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i)) β L
            (q3H3RangeFactor
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
                cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
              (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
                cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i)) β L u) c := by
        exact centeringMap_apply c _ y
      _ = q3Convolution β L h3Zero u y.1 -
          q3Convolution β L h3Zero u (cubeCenter (nativeHeatQ3RefinedCarrierChild m i)) := by
        rw [q3H3RangeValue_factor
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i)) β hab hcd L u y]
        rw [q3H3RangeValue_factor
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i)) β hab hcd L u c]
        rfl
  rw [childRemainderMap_apply U hU centers (old (parent u)) i x]
  have h_old_child :
      (old (parent u)) ⟨x.1, hU i x.2⟩ = parent u hxparent := by
    simp only [old, nativeHeatQ3RefinedCarrierParentRestrict,
      ContinuousMap.compCLM_apply]
    apply congrArg (parent u)
    apply Subtype.ext
    rfl
  have h_old_center : (old (parent u)) (centers i) = parent u hcenterParent := by
    change parent u
      ⟨(centers i).1,
        nativeHeatQ3RefinedCarrierDomain_subset_parent m (centers i).2⟩ =
      parent u hcenterParent
    apply congrArg (parent u)
    apply Subtype.ext
    simp [centers, nativeHeatQ3RefinedCarrierCenter, hcenterParent]
  rw [h_old_child, h_old_center]
  dsimp only [parent]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hparentValue hxparent, hparentValue hcenterParent]
  have h_child_map :
      nativeHeatQ3RefinedCarrierChildRectangleToCube m i
        (q3RemainderValueFactor
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
          (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
            cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i)) β L
          ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
            nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
            (subset_closure (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet
                (nativeHeatQ3RefinedCarrierChild m i)))⟩ u) x =
      q3RemainderValueFactor
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0)
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 0 +
          cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i))
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1)
        (cubeCorner (nativeHeatQ3RefinedCarrierChild m i) 1 +
          cubeScaleFactor (nativeHeatQ3RefinedCarrierChild m i)) β L
        ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
          nativeHeatQ3RefinedCarrierChild_closure_subset_rectangle m i
            (subset_closure (Algsuperdiff.Section3.Provider.Whitney.cubeCenter_mem_cubeSet
              (nativeHeatQ3RefinedCarrierChild m i)))⟩ u hxrect := by
    simp only [nativeHeatQ3RefinedCarrierChildRectangleToCube,
      ContinuousMap.compCLM_apply]
    apply congrArg
    apply Subtype.ext
    rfl
  rw [h_child_map, hchildValue hxrect]

end ASDExplicitGamma.Native
