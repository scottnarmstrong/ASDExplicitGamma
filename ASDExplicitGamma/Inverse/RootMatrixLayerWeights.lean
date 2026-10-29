module

public import ASDExplicitGamma.Inverse.WhitneyRootLayerCarrier
public import ASDExplicitGamma.Inverse.WeightedLocalizationResetSeries

/-! Literal fine-cell weights of each actual deterministic Whitney layer. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

/-- Actual physical fine-cell weights sum to the exact source layer fraction. -/
theorem root_matrix_layer_weights_sum (Q : TriadicCube 2) (H n : ℕ) :
    (∑ U ∈ whitneyRootLayer Q H (n+1), (volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) =
      bankLayerWeight n := by
  have hd : (whitneyRootLayer Q H (n+1):Set (TriadicCube 2)).PairwiseDisjoint cubeSet := by
    intro U hU V hV hne
    exact whitney_root_partition_disjoint Q H
      ((root_partition_iff_layer Q H U).mpr ⟨n+1,hU⟩)
      ((root_partition_iff_layer Q H V).mpr ⟨n+1,hV⟩) hne
  have hv := measureReal_biUnion_finset (μ := volume) hd (fun U _ => measurableSet_cubeSet U)
    (fun U _ => (volume_cubeSet_lt_top U).ne)
  change (volume (rootLayerCarrier Q H (n+1))).toReal =
    ∑ U ∈ whitneyRootLayer Q H (n+1), (volume (cubeSet U)).toReal at hv
  rw [← Finset.sum_div,← hv,root_layer_carrier_volume]
  exact mul_div_cancel_right₀ _ (by rw [volume_cubeSet_toReal]; exact (cubeVolume_pos Q).ne')

/-- Every cell of a given fine depth has its true exact volume weight. -/
theorem root_matrix_cell_weight {Q U : TriadicCube 2} (R : ℕ)
    (hU : U ∈ descendantsAtDepth Q R) :
    (volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal=(1/9:ℝ)^R := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
  rw [volume_cubeSet_toReal,volume_cubeSet_toReal,cubeVolume_eq_pow_scale,cubeVolume_eq_pow_scale,hs]
  rw [zpow_sub₀ (by norm_num : (3:ℝ)≠0),zpow_natCast,div_pow,div_div,one_div_pow]
  have hp : (9:ℝ)^R=((3:ℝ)^R)^2 := by rw [← pow_mul,Nat.mul_comm R 2,pow_mul]; norm_num
  rw [hp]
  field_simp

/-- The exact squared-weight sum, with no source layer envelope substituted. -/
theorem root_matrix_layer_squared_weights (Q : TriadicCube 2) (H n : ℕ) :
    (∑ U ∈ whitneyRootLayer Q H (n+1), ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)^2) =
      bankLayerWeight n*(1/9:ℝ)^(n+1+whitneyProfile H (n+1)) := by
  have he (U : TriadicCube 2) (hU : U ∈ whitneyRootLayer Q H (n+1)) :=
    root_matrix_cell_weight _ (root_whitney_layer_descendants Q H (n+1) hU)
  calc
    _ = ∑ U ∈ whitneyRootLayer Q H (n+1),
        ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*(1/9:ℝ)^(n+1+whitneyProfile H (n+1)) := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [pow_two,he U hU]
    _ = _ := by rw [← Finset.sum_mul,root_matrix_layer_weights_sum]

end
end ASDExplicitGamma.Inverse
