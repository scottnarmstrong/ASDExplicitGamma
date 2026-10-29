module

public import ASDExplicitGamma.Inverse.WhitneyMacroLayers
public import ASDExplicitGamma.Inverse.WhitneyLayerWeights
public import Algsuperdiff.Section3.Provider.Whitney.BoundaryDistance

/-! Exact planar layer masses of the actual source Whitney partition. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open Algsuperdiff.Section3.Provider

private theorem new_macro_mem_descendants (l : ℤ) (n : ℕ) {A : TriadicCube 2}
    (hA : A ∈ newMacroCubes l n) : A ∈ descendantsAtDepth (originCube 2 l) (n + 1) := by
  have hi : A ∈ interiorMacroCubes l (n + 1) := by
    rw [interior_next_partition]
    exact Finset.mem_union_left _ hA
  exact (Finset.mem_filter.mp hi).1

/-- Exact fine-layer count, retaining the source profile depth. -/
theorem whitney_layer_card (l : ℤ) (H n : ℕ) :
    (bankWhitneyLayer l H (n + 1)).card =
      (newMacroCubes l n).card * 9 ^ (whitneyProfile H (n + 1)) := by
  classical
  rw [whitney_layer_eq_macro_descendants, Finset.card_biUnion]
  · simp only [descendantsAtDepth_card, show (3 : ℕ) ^ 2 = 9 by norm_num,
      Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
  · intro A hA B hB hAB
    apply Finset.disjoint_left.mpr
    intro C hCA hCB
    have hd := pairwiseDisjoint_descendantsAtDepth (originCube 2 l) (n + 1)
      (new_macro_mem_descendants l n hA) (new_macro_mem_descendants l n hB) hAB
    have hx := Whitney.cubeCenter_mem_cubeSet C
    exact Set.disjoint_left.mp hd (cubeSet_subset_of_mem_descendantsAtDepth hCA hx)
      (cubeSet_subset_of_mem_descendantsAtDepth hCB hx)

/-- Fine subdivision preserves the exact macro-layer mass. -/
theorem whitney_layer_macro_mass (l : ℤ) (H n : ℕ) :
    (∑ P ∈ bankWhitneyLayer l H (n + 1), Whitney.cubeMassRatio (originCube 2 l) P) =
      ((newMacroCubes l n).card : ℝ) / (9 : ℝ) ^ (n + 1) := by
  have he (P : TriadicCube 2) (hP : P ∈ bankWhitneyLayer l H (n + 1)) :
      Whitney.cubeMassRatio (originCube 2 l) P =
        ((9 : ℝ) ^ (n + 1 + whitneyProfile H (n + 1)))⁻¹ := by
    have hs := Whitney.scale_eq_of_mem_whitneyLayer
      (show P ∈ Whitney.whitneyLayer l (whitneyProfile H) (n + 1) from hP)
    change P.scale = l - ((n + 1 : ℕ) : ℤ) - (whitneyProfile H (n + 1) : ℤ) at hs
    rw [Whitney.cubeMassRatio, hs]
    simp only [show (3 : ℝ) ^ 2 = 9 by norm_num, originCube]
    change (9 : ℝ) ^ (l - ((n + 1 : ℕ) : ℤ) - (whitneyProfile H (n + 1) : ℤ) - l) = _
    rw [show l - ((n + 1 : ℕ) : ℤ) - (whitneyProfile H (n + 1) : ℤ) - l =
      -(((n + 1 + whitneyProfile H (n + 1) : ℕ) : ℤ)) by omega,
      zpow_neg, zpow_natCast]
  rw [Finset.sum_congr rfl he, Finset.sum_const, nsmul_eq_mul, whitney_layer_card]
  push_cast
  rw [pow_add]
  field_simp

/-- The actual planar Whitney layer fractions are the exact corrected source
weights, not an upper bound that drops either geometric power. -/
theorem whitney_layer_mass (l : ℤ) (H n : ℕ) :
    (∑ P ∈ bankWhitneyLayer l H (n + 1), Whitney.cubeMassRatio (originCube 2 l) P) =
      bankLayerWeight n := by
  rw [whitney_layer_macro_mass]
  cases n with
  | zero => rw [new_macro_card_zero, layerWeight_zero]; norm_num
  | succ n =>
    rw [new_macro_card l (n + 1) (by omega), layerWeight_succ]
    rw [one_div_pow, one_div_pow]
    have hp : (9 : ℝ) ^ (n + 2) = (3 : ℝ) ^ (n + 2) * (3 : ℝ) ^ (n + 2) := by
      rw [← mul_pow]
      norm_num
    rw [hp]
    field_simp

/-- The geometric cube mass is the actual Lebesgue volume ratio. -/
theorem cubeMassRatio_eq_volume_ratio (Q R : TriadicCube 2) :
    Whitney.cubeMassRatio Q R = (volume (cubeSet R)).toReal / (volume (cubeSet Q)).toReal := by
  rw [Whitney.cubeMassRatio, volume_cubeSet_toReal, volume_cubeSet_toReal,
    cubeVolume_eq_pow_scale, cubeVolume_eq_pow_scale,
    zpow_sub₀ (by norm_num : (3 : ℝ) ^ 2 ≠ 0)]
  simp only [pow_two, mul_zpow]

/-- Actual Lebesgue volumes of the finalized fine cells give precisely the
corrected planar layer fraction in the root. -/
theorem whitney_layer_volume_fraction (l : ℤ) (H n : ℕ) :
    (∑ P ∈ bankWhitneyLayer l H (n + 1), (volume (cubeSet P)).toReal) /
        (volume (cubeSet (originCube 2 l))).toReal = bankLayerWeight n := by
  rw [Finset.sum_div]
  simp_rw [← cubeMassRatio_eq_volume_ratio]
  exact whitney_layer_mass l H n

end ASDExplicitGamma.Inverse
