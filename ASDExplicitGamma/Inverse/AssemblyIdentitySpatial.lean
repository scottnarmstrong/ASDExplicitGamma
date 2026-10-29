module

public import ASDExplicitGamma.Inverse.AssemblySpatialHolder
public import ASDExplicitGamma.Inverse.AssemblyShearedMean
public import ASDExplicitGamma.Inverse.WhitneyRootTranslation
public import ASDExplicitGamma.Inverse.AssemblyPhysicalBand

/-! The identity-layer shear means are paid by the actual root spatial wave. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open ASDExplicitGamma.Triadic.Support.ProjectedPoincare
open Function
open scoped ENNReal
noncomputable section

/-- Exact root-weighted integration over one disjoint Whitney layer. -/
theorem assembly_layer_weighted_cube_average (Q : TriadicCube 2) (H n : ℕ)
    (f : Vec 2 → ℝ) (hf : IntegrableOn f (rootLayerCarrier Q H n)) :
    (∑ U ∈ whitneyRootLayer Q H n,
      ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*cubeAverage U f) =
      ∫ x in rootLayerCarrier Q H n, f x ∂normalizedCubeMeasure Q := by
  classical
  have hsub (U : TriadicCube 2) (hU : U ∈ whitneyRootLayer Q H n) :
      cubeSet U ⊆ rootLayerCarrier Q H n := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨U,hU,hx⟩
  have hdis : Set.Pairwise (↑(whitneyRootLayer Q H n) : Set (TriadicCube 2))
      (fun U V => Disjoint (cubeSet U) (cubeSet V)) := by
    intro U hU V hV hne
    exact whitney_root_partition_disjoint Q H
      ((root_partition_iff_layer Q H U).mpr ⟨n,hU⟩)
      ((root_partition_iff_layer Q H V).mpr ⟨n,hV⟩) hne
  have hsum := integral_biUnion_finset (μ := volume) (whitneyRootLayer Q H n)
    (fun U _ => measurableSet_cubeSet U) hdis (fun U hU => hf.mono_set (hsub U hU))
  have hEQ : rootLayerCarrier Q H n ⊆ cubeSet Q :=
    (root_layer_carrier_subset_open Q H n).trans (openCubeSet_subset_cubeSet Q)
  rw [assembly_normalized_layer_integral Q _ hEQ]
  change _ = (∫ x in ⋃ U ∈ whitneyRootLayer Q H n, cubeSet U, f x ∂volume)/_
  rw [hsum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro U hU
  unfold cubeAverage
  rw [volume_cubeSet_toReal]
  have hv := (cubeVolume_pos U).ne'
  field_simp [hv]

/-- Squared local physical means on the whole deterministic identity layer
are bounded by the same layer's spatial squared band. -/
theorem assembly_layer_mean_square_le_spatial (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (N : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    let j := layerOldCutoff Q.scale H (i+1)
    assemblyLayerMeanSquare M Q H (i+1) N weights ω ≤
      (1/(Annealed.sigmaBar M j)^2)*
        ∫ x in rootLayerCarrier Q H (i+1), (laterScalarBand j N weights ω x)^2
          ∂normalizedCubeMeasure Q := by
  dsimp only
  let j := layerOldCutoff Q.scale H (i+1)
  let f := laterScalarBand j N weights ω
  have htop : MemLp f ⊤ (normalizedCubeMeasure Q) := by
    change MemLp (laterScalarBand j N weights ω) ⊤ (normalizedCubeMeasure Q)
    rw [← later_band_w2_value Q j N weights ω]
    exact PlanarW2Infinity.value_memLp_top_normalized _
  have hfi : IntegrableOn (fun x => f x^2) (cubeSet Q) :=
    integrableOn_of_integrable_normalizedCubeMeasure Q
      ((assembly_square_memLp_two _ _ htop).integrable (by norm_num))
  have hEQ : rootLayerCarrier Q H (i+1) ⊆ cubeSet Q :=
    (root_layer_carrier_subset_open Q H (i+1)).trans (openCubeSet_subset_cubeSet Q)
  have hsum := assembly_layer_weighted_cube_average Q H (i+1)
    (fun x => f x^2) (hfi.mono_set hEQ)
  calc
    _ ≤ ∑ U ∈ whitneyRootLayer Q H (i+1),
        ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*
          ((1/(Annealed.sigmaBar M j)^2)*cubeAverage U (fun x => f x^2)) := by
      apply Finset.sum_le_sum
      intro U hU
      have hl := root_whitney_old_cutoff_eq Q H (i+1) hU
      have hmean := cubeAverage_sq_le U (laterBandW2 U j N weights ω).value.memL2_normalizedCubeMeasure
      rw [later_band_w2_value] at hmean
      apply mul_le_mul_of_nonneg_left _ (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      rw [assembly_physical_average_eq_cubeAverage,← hl,later_band_w2_value,div_pow]
      change (cubeAverage U f)^2/(Annealed.sigmaBar M j)^2 ≤ _
      exact (div_le_div_of_nonneg_right hmean (sq_nonneg _)).trans_eq (by ring)
    _ = _ := by
      rw [show (∑ U ∈ whitneyRootLayer Q H (i+1),
        ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*
          ((1/(Annealed.sigmaBar M j)^2)*cubeAverage U (fun x => f x^2))) =
        (1/(Annealed.sigmaBar M j)^2)*(∑ U ∈ whitneyRootLayer Q H (i+1),
          ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*cubeAverage U (fun x => f x^2)) by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro U _
            ring,hsum]

/-- The actual identity-layer squared means retain the square root of the
exact layer fraction, with the root physical missing wave in the true frame. -/
theorem assembly_layer_mean_square_le_physical_wave
    (M : ABKModel 2) (Q : TriadicCube 2) (H i : ℕ) (N : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    assemblyLayerMeanSquare M Q H (i+1) N weights ω ≤
      Real.sqrt (bankLayerWeight i)*
        physicalMissingWave M (layerOldCutoff Q.scale H (i+1)) Q.scale N
          (cubeCorner Q 0) (cubeCorner Q 1) weights ω/2 := by
  let j := layerOldCutoff Q.scale H (i+1)
  let f := laterScalarBand j N weights ω
  let E := rootLayerCarrier Q H (i+1)
  let μ := normalizedCubeMeasure Q
  have hf : MemLp f ⊤ μ := by
    change MemLp (laterScalarBand j N weights ω) ⊤ (normalizedCubeMeasure Q)
    rw [← later_band_w2_value Q j N weights ω]
    exact PlanarW2Infinity.value_memLp_top_normalized _
  have hc : MemLp (fun _ : Vec 2 => (1:ℝ)^2) 2 μ := by
    simpa only [one_pow] using (memLp_const (1:ℝ) : MemLp (fun _ : Vec 2 => (1:ℝ)) 2 μ)
  have hh := assembly_spatial_square_product_le μ E f (fun _ => 1)
    (assembly_square_memLp_two μ f hf) hc
  simp only [one_pow,mul_one,integral_const] at hh
  have hvol : (μ E).toReal=bankLayerWeight i := by
    have hEQ : E ⊆ cubeSet Q :=
      (root_layer_carrier_subset_open Q H (i+1)).trans (openCubeSet_subset_cubeSet Q)
    have hv := assembly_normalized_layer_integral Q E hEQ (fun _ => 1)
    simp only [integral_const,smul_eq_mul,mul_one,Measure.real,
      Measure.restrict_apply MeasurableSet.univ,Set.univ_inter] at hv
    change (μ E).toReal=(volume (rootLayerCarrier Q H (i+1))).toReal/(volume (cubeSet Q)).toReal at hv
    rw [root_layer_carrier_volume] at hv
    have hV : (volume (cubeSet Q)).toReal ≠ 0 := by
      rw [volume_cubeSet_toReal]; exact (cubeVolume_pos Q).ne'
    exact hv.trans (mul_div_cancel_right₀ _ hV)
  rw [Measure.real,smul_eq_mul,mul_one,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,hvol] at hh
  have hs := assembly_layer_mean_square_le_spatial M Q H i N weights ω
  rw [later_band_physical_missing_wave_eq_fourth_average,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  exact hs.trans ((mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring))

end
end ASDExplicitGamma.Inverse
