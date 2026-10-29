module

public import ASDExplicitGamma.Inverse.FullResponseActiveSpatialDensity
public import ASDExplicitGamma.Inverse.RootMatrixLayerWeights

/-! Exact Whitney-layer spatial pairing for the active trace coefficients. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory

noncomputable section

/-- The physical weights convert a complete Whitney layer's cube averages
to precisely its integral divided by the root volume. -/
theorem root_layer_weighted_cube_average_eq (Q : TriadicCube 2) (H n : ℕ)
    (f : Vec 2 → ℝ) (hf : IntegrableOn f (rootLayerCarrier Q H (n+1))) :
    (∑ U ∈ whitneyRootLayer Q H (n+1),
      ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) * cubeAverage U f) =
      (∫ x in rootLayerCarrier Q H (n+1), f x)/(volume (cubeSet Q)).toReal := by
  classical
  have hdisj : (whitneyRootLayer Q H (n+1) : Set (TriadicCube 2)).PairwiseDisjoint
      cubeSet := by
    intro U hU V hV hne
    exact whitney_root_partition_disjoint Q H
      ((root_partition_iff_layer Q H U).mpr ⟨n+1, hU⟩)
      ((root_partition_iff_layer Q H V).mpr ⟨n+1, hV⟩) hne
  have hsplit := integral_biUnion_finset (whitneyRootLayer Q H (n+1))
    (fun U _ => measurableSet_cubeSet U) hdisj
    (fun U hU => hf.mono_set (fun x hx => Set.mem_iUnion₂.mpr ⟨U, hU, hx⟩))
  change (∫ x in rootLayerCarrier Q H (n+1), f x) = _ at hsplit
  rw [hsplit, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro U hU
  rw [volume_cubeSet_toReal, volume_cubeSet_toReal, cubeAverage]
  field_simp [(cubeVolume_pos U).ne', (cubeVolume_pos Q).ne']

/-- The active parent wave means pair with the density squares in space.
Exact parent volumes remain on both fourth moments; no count factor occurs. -/
theorem root_layer_wave_density_spatial_holder
    (Q : TriadicCube 2) (H n : ℕ) (f g : Vec 2 → ℝ)
    (hf4 : IntegrableOn (fun x => f x^4) (rootLayerCarrier Q H (n+1)))
    (hg4 : IntegrableOn (fun x => g x^4) (rootLayerCarrier Q H (n+1)))
    (hlocal : ∀ U ∈ whitneyRootLayer Q H (n+1),
      MemLp f 2 (normalizedCubeMeasure U) ∧
      MemLp (fun x => f x^2) 2 (normalizedCubeMeasure U) ∧
      MemLp (fun x => g x^2) 2 (normalizedCubeMeasure U)) :
    (∑ U ∈ whitneyRootLayer Q H (n+1),
      ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) *
        ((cubeAverage U f)^2 * cubeAverage U (fun x => g x^2))) ≤
      Real.sqrt ((∫ x in rootLayerCarrier Q H (n+1), f x^4)/
        (volume (cubeSet Q)).toReal) *
      Real.sqrt ((∫ x in rootLayerCarrier Q H (n+1), g x^4)/
        (volume (cubeSet Q)).toReal) := by
  classical
  let s := whitneyRootLayer Q H (n+1)
  let w := fun U : TriadicCube 2 =>
    (volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal
  let a := fun U : TriadicCube 2 => cubeAverage U (fun x => f x^4)
  let b := fun U : TriadicCube 2 => cubeAverage U (fun x => g x^4)
  have hw (U : TriadicCube 2) : 0 ≤ w U :=
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have ha (U : TriadicCube 2) : 0 ≤ a U := by
    dsimp only [a, cubeAverage]
    exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos U).le)
      (integral_nonneg fun x => by positivity)
  have hb (U : TriadicCube 2) : 0 ≤ b U := by
    dsimp only [b, cubeAverage]
    exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos U).le)
      (integral_nonneg fun x => by positivity)
  have hcs := weighted_finset_sqrt_product_le s w a b hw ha hb
  have hA := root_layer_weighted_cube_average_eq Q H n (fun x => f x^4) hf4
  have hB := root_layer_weighted_cube_average_eq Q H n (fun x => g x^4) hg4
  calc
    _ ≤ ∑ U ∈ s, w U * Real.sqrt (a U * b U) := by
      apply Finset.sum_le_sum
      intro U hU
      apply mul_le_mul_of_nonneg_left _ (hw U)
      exact cube_average_wave_density_product_le_fourth U f g
        (hlocal U hU).1 (hlocal U hU).2.1 (hlocal U hU).2.2
    _ ≤ Real.sqrt (∑ U ∈ s, w U*a U) * Real.sqrt (∑ U ∈ s, w U*b U) := hcs
    _ = _ := by
      dsimp only [s, w, a, b]
      rw [hA, hB]

/-- The wave fourth moment can be enlarged to the whole observer root,
while the density keeps the small Whitney-layer volume. -/
theorem root_layer_wave_density_spatial_holder_root
    (Q : TriadicCube 2) (H n : ℕ) (f g : Vec 2 → ℝ)
    (hf4 : IntegrableOn (fun x => f x^4) (cubeSet Q))
    (hg4 : IntegrableOn (fun x => g x^4) (rootLayerCarrier Q H (n+1)))
    (hlocal : ∀ U ∈ whitneyRootLayer Q H (n+1),
      MemLp f 2 (normalizedCubeMeasure U) ∧
      MemLp (fun x => f x^2) 2 (normalizedCubeMeasure U) ∧
      MemLp (fun x => g x^2) 2 (normalizedCubeMeasure U)) :
    (∑ U ∈ whitneyRootLayer Q H (n+1),
      ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal) *
        ((cubeAverage U f)^2 * cubeAverage U (fun x => g x^2))) ≤
      Real.sqrt (cubeAverage Q (fun x => f x^4)) *
        Real.sqrt ((∫ x in rootLayerCarrier Q H (n+1), g x^4)/
          (volume (cubeSet Q)).toReal) := by
  have hsub := (root_layer_carrier_subset_open Q H (n+1)).trans
    (openCubeSet_subset_cubeSet Q)
  have hlocalbound := root_layer_wave_density_spatial_holder Q H n f g
    (hf4.mono_set hsub) hg4 hlocal
  have hi : (∫ x in rootLayerCarrier Q H (n+1), f x^4) ≤
      ∫ x in cubeSet Q, f x^4 :=
    setIntegral_mono_set hf4 (Filter.Eventually.of_forall fun x => by positivity)
      (Filter.Eventually.of_forall fun x hx => hsub hx)
  have hm : (∫ x in rootLayerCarrier Q H (n+1), f x^4)/
      (volume (cubeSet Q)).toReal ≤ cubeAverage Q (fun x => f x^4) := by
    rw [cubeAverage, ← volume_cubeSet_toReal]
    simpa only [div_eq_mul_inv, mul_comm] using
      div_le_div_of_nonneg_right hi (ENNReal.toReal_nonneg (a := volume (cubeSet Q)))
  exact hlocalbound.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt hm) (Real.sqrt_nonneg _))

end
end ASDExplicitGamma.Inverse
