module

public import ASDExplicitGamma.Inverse.StoppedFineConnectivity
public import ASDExplicitGamma.Inverse.StoppedQ3Height
public import ASDExplicitGamma.Inverse.WhitneyRootTiles

/-! The actual stopped event bounds fine occupied paths starting anywhere
in the root. This is the deterministic input to the two-layer argument. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
noncomputable section

/-- The root starting population contains every actual depth-h descendant,
with the exact centered triadic indexing and actual block division. -/
theorem root_block_start_covers (Q : TriadicCube 2) (h : ℕ)
    {A : TriadicCube 2} (hA : A ∈ descendantsAtDepth Q h) :
    ∃ i : RootStartingIndex h, rootBlockStart Q h i = fineBlockIndex A.index := by
  have hb := Whitney.abs_index_sub_le_of_mem_descendantsAtDepth hA
  have hE := Whitney.two_mul_extremeIdx_add_one h
  have hE0 := Whitney.extremeIdx_nonneg h
  let i : RootStartingIndex h := fun d =>
    ⟨(A.index d-(3^h:ℤ)*Q.index d+Whitney.extremeIdx h).toNat,by
      have hd := abs_le.mp (hb d)
      have hp : (0:ℤ) < 3^h := pow_pos (by norm_num) _
      have hpNat : ((3^h:ℕ):ℤ) = 3^h := by norm_cast
      omega⟩
  refine ⟨i,?_⟩
  apply congrArg fineBlockIndex
  funext d
  have hd := abs_le.mp (hb d)
  have he : ((A.index d-(3^h:ℤ)*Q.index d+Whitney.extremeIdx h).toNat:ℤ) =
      A.index d-(3^h:ℤ)*Q.index d+Whitney.extremeIdx h := Int.toNat_of_nonneg (by omega)
  change (3^h:ℤ)*Q.index d+(i d).val-((3^h:ℤ)-1)/2 = A.index d
  dsimp only [i]
  omega

/-- On successful separation, every occupied fine path rooted at an actual
root descendant has coordinate diameter below the source 3^(h/4) threshold. -/
theorem successful_separation_fine_distance {Ω : Type*} (B : PlanarMarks Ω)
    (ω : Ω) (Q : TriadicCube 2) (h : ℕ) (hh : 333 ≤ h)
    (hgood : ω ∉ separationFailure B h (rootBlockStart Q h))
    {A : TriadicCube 2} (hA : A ∈ descendantsAtDepth Q h)
    {x y : fineOccupied B ω} (hx : x.val = A.index)
    (hxy : (fineGraph.induce (fineOccupied B ω)).Reachable x y) (d : Fin 2) :
    (|y.val d-x.val d|:ℝ) < (3:ℝ)^((h:ℝ)/4) := by
  obtain ⟨i,hi⟩ := root_block_start_covers Q h hA
  have hblock : |fineBlockIndex y.val d-fineBlockIndex x.val d| < (separationRadius h:ℤ) := by
    by_contra hn
    apply hgood
    apply Set.mem_iUnion.mpr
    refine ⟨i,?_⟩
    rw [hi,← hx]
    exact fine_reachable_reaches B ω hxy _ ⟨d,by omega⟩
  have hendpoint := fine_block_endpoint_distance x.val y.val d
  have hbR : (|fineBlockIndex y.val d-fineBlockIndex x.val d|:ℝ)+1 ≤
      (separationRadius h:ℝ) := by exact_mod_cast (show
        |fineBlockIndex y.val d-fineBlockIndex x.val d|+1 ≤ (separationRadius h:ℤ) by omega)
  have heR : (|y.val d-x.val d|:ℝ) < (2*3^40:ℝ)*
      ((|fineBlockIndex y.val d-fineBlockIndex x.val d|:ℝ)+1) := by exact_mod_cast hendpoint
  have hY := height_exponent_lower h hh
  have hf : (separationRadius h:ℝ) ≤ heightExponent h/3-1 :=
    Nat.floor_le (by norm_num at hY ⊢; linarith only [hY])
  have hmul := mul_le_mul_of_nonneg_left (hbR.trans hf) (by norm_num : (0:ℝ) ≤ 2*3^40)
  have hphysical : (3:ℝ)^((h:ℝ)/4) = (3:ℝ)^40*heightExponent h := by
    unfold heightExponent
    rw [← Real.rpow_natCast (3:ℝ) 40,← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    congr 1
    ring
  rw [hphysical]
  norm_num at hmul heR hY ⊢
  linarith only [hmul,heR,hY]

end
end ASDExplicitGamma.Inverse
