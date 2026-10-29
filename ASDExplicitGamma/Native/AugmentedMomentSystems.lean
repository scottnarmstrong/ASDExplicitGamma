module

public import ASDExplicitGamma.Numerics.Native.Systems

/-! # The native 153-system augmented heat interface -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native Matrix

/-- Every configured native system has the producer's nonnegative initial
vector, scaled subdiagonal and forcing bounds, and row-sum bound. -/
theorem augmentedMomentSystem_bounds (j : Fin 153) :
    (∀ i : Fin 21, 0 ≤ (nativeConfiguredSystem j).system.v.getD i.val 0 ∧
      (nativeConfiguredSystem j).system.v.getD i.val 0 ≤ 1) ∧
    (∀ i : Fin 21, 0 ≤ (nativeConfiguredSystem j).system.subdiag.getD i.val 0 ∧
      (nativeConfiguredSystem j).system.subdiag.getD i.val 0 ≤ 1/2) ∧
    (∀ i : Fin 21, 0 ≤ (nativeConfiguredSystem j).system.diag.getD i.val 0 ∧
      0 ≤ (nativeConfiguredSystem j).system.force.getD i.val 0 ∧
      (nativeConfiguredSystem j).system.force.getD i.val 0 ≤ (1/2 : ℚ)^i.val) ∧
    (∀ i : Fin 21, (nativeConfiguredSystem j).system.subdiag.getD i.val 0 +
      (nativeConfiguredSystem j).system.diag.getD i.val 0 +
      (nativeConfiguredSystem j).system.force.getD i.val 0 ≤ 6) := by
  exact ⟨(nativeConfiguredSystem j).initial, (nativeConfiguredSystem j).subdiag,
    (nativeConfiguredSystem j).force, (nativeConfiguredSystem j).rows⟩

/-- The augmented matrix is nonnegative and has row sums at most six. -/
theorem augmentedMomentMatrix_nonneg (j : Fin 153) :
    ∀ i k, 0 ≤ nativeSystemMatrix (nativeConfiguredSystem j).system i k := by
  apply nativeSystemMatrix_nonneg
  · exact fun i => ((augmentedMomentSystem_bounds j).2.2.1 i).1
  · exact fun i => ((augmentedMomentSystem_bounds j).2.1 i).1
  · exact fun i => ((augmentedMomentSystem_bounds j).2.2.1 i).2.1

theorem augmentedMomentMatrix_row_sum (j : Fin 153) :
    ∀ i, ∑ k, nativeSystemMatrix (nativeConfiguredSystem j).system i k ≤ 6 := by
  apply nativeSystemMatrix_row_sum
  intro i
  have h := (augmentedMomentSystem_bounds j).2.2.2 i
  nlinarith [h]

/-- The augmented coordinate is fixed at one in every producer initial vector. -/
theorem augmentedMomentSystem_first_coordinate (j : Fin 153) :
    (nativeConfiguredSystem j).system.v.getD 0 0 = 1 := by
  have hmap : nativeAllSystems.map (fun c => c.system.v.getD 0 0) =
      List.replicate 153 1 := by
    decide +kernel
  have h := congrArg (fun xs : List ℚ =>
      xs.getD j.val (nativeGap001Certificate.system.v.getD 0 0)) hmap
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    Option.getD_map, List.getElem?_replicate, j.isLt] at h
  simpa [nativeConfiguredSystem] using h

/-- All configured results retain their componentwise outward replay bound. -/
theorem augmentedMomentSystem_replay (j : Fin 153) (i : Fin 21) :
    (NormedSpace.exp (nativeSystemMatrix (nativeConfiguredSystem j).system) *ᵥ
      nativeVectorReal (nativeConfiguredSystem j).system.v) i ≤
        nativeVectorReal (nativeConfiguredSystem j).result i :=
  native_configured_system_replay j i

end ASDExplicitGamma.Native
