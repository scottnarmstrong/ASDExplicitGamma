module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalBandSplit
public import ASDExplicitGamma.Triadic.PoincareCell

/-! Measurability and the pathwise Jensen inequality for the actual physical
potential mean used by the canonical trial-field gauge. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Triadic
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
noncomputable section

/-- Each coordinate of the actual physical mean is strongly measurable on the
original cutoff sample space. -/
theorem upper_cell_physical_potential_mean_measurable
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) (i : Fin 2) :
    StronglyMeasurable (fun ω => upperCellPhysicalPotentialMean M n terminal c e Q ω i) := by
  have hm : StronglyMeasurable
      (fun ω => (upperCellPotentialRepr M n terminal c e ω).ofLp i) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).continuous.comp_stronglyMeasurable
      (upper_cell_potential_repr_measurable M n terminal c e)
  unfold upperCellPhysicalPotentialMean cubeAverage
  exact ((stronglyMeasurable_uncurry_realize hm).integral_prod_right'
    (ν := volume.restrict (cubeSet Q))).const_mul _

/-- Spatial Jensen bounds the squared norm of the canonical physical mean by
physical averages of the same correction-coordinate squares, retaining all
spatial and cross-coordinate correlations. -/
theorem upper_cell_physical_potential_mean_jensen
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (∑ i : Fin 2, (upperCellPhysicalPotentialMean M n terminal c e Q ω i)^2) ≤
        ∑ i : Fin 2, cubeAverage Q (fun x =>
          ((realize (upperCellPotentialRepr M n terminal c e) ω x).ofLp i)^2) := by
  have hl := ae_memLp_two_realize (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (volume_openCubeSet_lt_top Q).ne (upper_cell_potential_repr_measurable M n terminal c e)
    (upper_cell_potential_repr_memLp M n terminal c e)
  filter_upwards [hl] with ω hω
  apply Finset.sum_le_sum
  intro i _
  have hi : MemLp (fun x => (realize (upperCellPotentialRepr M n terminal c e) ω x).ofLp i)
      2 (volume.restrict (openCubeSet Q)) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).comp_memLp' hω
  have hn := memLp_normalized_of_memL2On hi
  have hj := energy_projection_le Q 0 hn
  rw [energy_projection_zero] at hj
  simpa only [upperCellPhysicalPotentialMean,energy,pairing,←pow_two] using hj

end
end ASDExplicitGamma.Scalar
