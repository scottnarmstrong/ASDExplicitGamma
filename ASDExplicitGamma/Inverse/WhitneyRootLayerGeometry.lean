module

public import ASDExplicitGamma.Inverse.WhitneyRootTranslation
public import Algsuperdiff.Section3.Provider.Whitney.BoundaryDistance

/-! Exact finite layers at arbitrary physical triadic roots. Translation is
performed on the actual cubes, retaining their centered fine-grid indices. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

/-- The physical root translation, as a total map on fine cubes. -/
def rootTranslateCube (Q P : TriadicCube 2) : TriadicCube 2 :=
  translateCube (descendantTranslationShift (Q.scale-P.scale).toNat Q.index) P

/-- Actual translated finite Whitney layer; its union is the already defined
physical root partition. -/
def whitneyRootLayer (Q : TriadicCube 2) (H n : ℕ) : Finset (TriadicCube 2) :=
  (bankWhitneyLayer Q.scale H n).image (rootTranslateCube Q)

theorem root_translate_cube_scale (Q P : TriadicCube 2) :
    (rootTranslateCube Q P).scale = P.scale := rfl

/-- Fine cubes are moved by exactly the same physical vector as their root. -/
theorem root_translate_cube_center (Q P : TriadicCube 2) (hP : P.scale ≤ Q.scale) :
    cubeCenter (rootTranslateCube Q P) = cubeCenter P+triadicCubeShift Q := by
  have hp : (3:ℝ)^(Q.scale-P.scale).toNat*(3:ℝ)^P.scale = (3:ℝ)^Q.scale := by
    rw [← zpow_natCast,← zpow_add₀ (by norm_num : (3:ℝ) ≠ 0)]
    congr 1
    omega
  funext d
  simp only [rootTranslateCube,translateCube,cubeCenter,cubeScaleFactor,
    descendantTranslationShift,Pi.add_apply,triadicCubeShift,Int.cast_add,Int.cast_mul,
    Int.cast_pow,Int.cast_ofNat]
  rw [add_mul]
  calc
    _ = (P.index d:ℝ)*(3:ℝ)^P.scale+(Q.index d:ℝ)*((3:ℝ)^(Q.scale-P.scale).toNat*(3:ℝ)^P.scale) := by ring
    _ = _ := by rw [hp]

/-- The physical translate of an actual root descendant is an actual
descendant of the physical root at the same generation depth. -/
theorem root_translate_descendant (Q : TriadicCube 2) {n : ℕ} {P : TriadicCube 2}
    (hP : P ∈ descendantsAtDepth (originCube 2 Q.scale) n) :
    rootTranslateCube Q P ∈ descendantsAtDepth Q n := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hP
  change P.scale = Q.scale-n at hs
  have hd : (Q.scale-P.scale).toNat = n := by omega
  have hroot : translateCube Q.index (originCube 2 Q.scale) = Q := by
    cases Q
    simp only [translateCube,originCube,Pi.zero_apply,zero_add]
  have hh : translateCube (descendantTranslationShift n Q.index) P ∈
      descendantsAtDepth (translateCube Q.index (originCube 2 Q.scale)) n := by
    rw [descendantsAtDepth_translateCube]
    exact Finset.mem_image.mpr ⟨P,hP,rfl⟩
  rw [hroot] at hh
  simpa only [rootTranslateCube,hd] using hh

theorem root_whitney_layer_descendants (Q : TriadicCube 2) (H n : ℕ)
    {V : TriadicCube 2} (hV : V ∈ whitneyRootLayer Q H n) :
    V ∈ descendantsAtDepth Q (n+whitneyProfile H n) := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hV
  exact root_translate_descendant Q (mem_descendantsAtDepth_of_mem_whitneyLayer hP)

theorem root_whitney_layer_scale (Q : TriadicCube 2) (H n : ℕ)
    {V : TriadicCube 2} (hV : V ∈ whitneyRootLayer Q H n) :
    V.scale = Q.scale-n-whitneyProfile H n := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth (root_whitney_layer_descendants Q H n hV)
  push_cast at hs
  omega

theorem root_translate_touch_iff (Q P R : TriadicCube 2)
    (hP : P.scale ≤ Q.scale) (hR : R.scale ≤ Q.scale) :
    CubeTouch (rootTranslateCube Q P) (rootTranslateCube Q R) ↔ CubeTouch P R := by
  simp only [cubeTouch_iff,root_translate_cube_center Q P hP,root_translate_cube_center Q R hR,
    Pi.add_apply,add_sub_add_right_eq_sub,cubeRadius_eq_zpow_div_two,root_translate_cube_scale]

/-- The exact two-thirds macro-layer gap survives physical root translation. -/
theorem root_whitney_layer_gap (Q : TriadicCube 2) (H a n : ℕ) (han : a+2 ≤ n)
    {A D : TriadicCube 2} (hA : A ∈ whitneyRootLayer Q H a)
    (hD : D ∈ whitneyRootLayer Q H n) :
    (2/3:ℝ)*(3:ℝ)^(Q.scale-(a:ℤ)) < ‖cubeCenter A-cubeCenter D‖ := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hD
  rw [root_translate_cube_center Q P (whitney_scale_le _ H ⟨a,hP⟩),
    root_translate_cube_center Q R (whitney_scale_le _ H ⟨n,hR⟩),add_sub_add_right_eq_sub]
  exact two_thirds_zpow_lt_norm_cubeCenter_sub_of_layers han hP hR

theorem root_whitney_touching_layers (Q : TriadicCube 2) (H a n : ℕ)
    {A D : TriadicCube 2} (hA : A ∈ whitneyRootLayer Q H a)
    (hD : D ∈ whitneyRootLayer Q H n) (ht : CubeTouch A D) :
    a ≤ n+1 ∧ n ≤ a+1 := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hD
  have ht' := (root_translate_touch_iff Q P R (whitney_scale_le _ H ⟨a,hP⟩)
    (whitney_scale_le _ H ⟨n,hR⟩)).mp ht
  exact whitneyLayer_index_close_of_cubeTouch (fun k => by unfold whitneyProfile; omega) hP hR ht'

/-- The existing physical root partition is precisely the union of these
actual finite layers. -/
theorem root_partition_iff_layer (Q : TriadicCube 2) (H : ℕ) (V : TriadicCube 2) :
    V ∈ whitneyRootPartition Q H ↔ ∃ n, V ∈ whitneyRootLayer Q H n := by
  constructor
  · rintro ⟨P,⟨n,hP⟩,rfl⟩
    exact ⟨n,Finset.mem_image.mpr ⟨P,hP,rfl⟩⟩
  · rintro ⟨n,hV⟩
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hV
    exact ⟨P,⟨n,hP⟩,rfl⟩

end
end ASDExplicitGamma.Inverse
