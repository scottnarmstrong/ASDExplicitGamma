module

public import ASDExplicitGamma.Inverse.FullResponseActiveSpatialHolder
public import ASDExplicitGamma.Inverse.LayerDensityComparison

/-! Finite block fields are locally bounded on every cube inside their root.
This gives the density-side spatial `L²` input to the active Holder step. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal

noncomputable section

/-- A root's finite physical-block field is in every finite local `Lᵖ`
space on any cube contained in that root. The proof uses the actual finite
block partition, not a moment or boundedness premise on the sample. -/
theorem root_block_field_memLp_top_on_cube
    (Q R : TriadicCube 2) (hRQ : cubeSet R ⊆ cubeSet Q) (depth : ℕ)
    (F : BlockSite → ℝ) :
    MemLp (fun x => F (physicalBlockIndex (rootFineLabel Q depth) x)) ⊤
      (normalizedCubeMeasure R) := by
  classical
  let μ := normalizedCubeMeasure R
  let P := rootBlockPopulation Q depth
  let f : Vec 2 → ℝ := fun x => F (physicalBlockIndex (rootFineLabel Q depth) x)
  let term : P → Vec 2 → ℝ := fun z =>
    (cubeSet Q ∩ physicalBlockSet (rootFineLabel Q depth) z.1).indicator
      (fun _ => F z.1)
  have hμmem : ∀ᵐ x ∂μ, x ∈ cubeSet Q := by
    have hbase : ∀ᵐ x ∂(volume.restrict (cubeSet R)), x ∈ cubeSet Q := by
      filter_upwards [ae_restrict_mem (measurableSet_cubeSet R)] with x hx
      exact hRQ hx
    change ∀ᵐ x ∂(ENNReal.ofReal ((cubeVolume R)⁻¹) •
      volume.restrict (cubeSet R)), x ∈ cubeSet Q
    exact Measure.ae_smul_measure hbase _
  have hterm (z : P) : MemLp (term z) ⊤ μ := by
    exact memLp_indicator_const ⊤ ((measurableSet_cubeSet Q).inter
        (physical_block_set_measurable _ _))
      (F z.1) (Or.inr (measure_lt_top μ (cubeSet Q ∩
        physicalBlockSet (rootFineLabel Q depth) z.1)).ne)
  have hsum_aux (s : Finset P) :
      MemLp (fun x => ∑ z ∈ s, term z x) ⊤ μ := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert z s hz ih =>
        have hform : (fun x => ∑ y ∈ insert z s, term y x) =
            term z + (fun x => ∑ y ∈ s, term y x) := by
          funext x
          simp only [Finset.sum_insert hz, Pi.add_apply]
        rw [hform]
        exact (hterm z).add ih
  have hsum : MemLp (fun x => ∑ z : P, term z x) ⊤ μ := by
    simpa using hsum_aux Finset.univ
  have hrepr := root_layer_indicator_eq Q depth (cubeSet Q) (by intro x hx; exact hx)
    F
  have hEq : f =ᵐ[μ] (fun x => ∑ z : P, term z x) := by
    filter_upwards [hμmem] with x hx
    change F (physicalBlockIndex (rootFineLabel Q depth) x) = _
    have hpoint := congrFun hrepr x
    rw [Set.indicator_of_mem hx] at hpoint
    exact hpoint
  apply memLp_iff.mpr
  rw [eLpNorm_congr_ae hEq]
  exact hsum.eLpNorm_lt_top

/-- Each of the three actual reset-density resolutions is locally square
integrable on every cube contained in the root, at every sample. -/
theorem layer_resolution_density_square_memLp
    (M : ABKModel 2) (Q R : TriadicCube 2) (hRQ : cubeSet R ⊆ cubeSet Q)
    (H0 : ℕ) (hH0 : 333 ≤ H0) (hk : ℕ × ℕ) (τ η : ℝ)
    (e : Fin 3) (ω : Cutoff.CutoffSample 2) :
    MemLp (fun x => (layerResolutionDiameter M Q (H0+hk.1) τ η
      (hk.2+1) e ω x)^2) 2 (normalizedCubeMeasure R) := by
  let d : Vec 2 → ℝ := fun x =>
    realDiameterField
      (q3PlanarMarks M (rootFineLabel Q (resetDensityDepth H0 hk e)) τ η)
      (physicalBlockIndex (rootFineLabel Q (resetDensityDepth H0 hk e)) x) ω
  have htop := root_block_field_memLp_top_on_cube Q R hRQ
    (resetDensityDepth H0 hk e)
    (fun z => realDiameterField
      (q3PlanarMarks M (rootFineLabel Q (resetDensityDepth H0 hk e)) τ η) z ω)
  have hfour : MemLp d 4 (normalizedCubeMeasure R) := by
    simpa only [d] using htop.mono_exponent (by norm_num)
  have hfourSq := hfour.norm_rpow_div (ENNReal.ofReal 2)
  have hdiv : (4:ℝ≥0∞) / ENNReal.ofReal (2:ℝ) = 2 := by
    rw [show (4:ℝ≥0∞) = ENNReal.ofReal (4:ℝ) by norm_num]
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [hdiv] at hfourSq
  rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2)] at hfourSq
  have hpowEq : (fun x => ‖d x‖ ^ (2:ℝ)) = fun x => d x ^ 2 := by
    funext x
    change |d x| ^ 2 = d x ^ 2
    rw [Real.rpow_two]
    exact sq_abs (d x)
  have hfourSq' : MemLp (fun x => d x ^ 2) 2 (normalizedCubeMeasure R) := by
    rw [← hpowEq]
    exact hfourSq
  have hlabel := layer_resolution_density_label Q H0 hH0 hk e
  simpa only [d, layerResolutionDiameter, hlabel] using hfourSq'

end
end ASDExplicitGamma.Inverse
