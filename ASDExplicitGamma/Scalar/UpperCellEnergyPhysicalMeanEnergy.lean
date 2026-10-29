module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalSquareMoment

/-! Second moments of the literal physical potential mean. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
noncomputable section

/-- Each actual cube-mean coordinate is square integrable and its energy
contracts the stationary coordinate energy. -/
theorem upper_cell_physical_mean_coordinate_energy
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) (i : Fin 2) :
    let Y := fun ω => upperCellPhysicalPotentialMean M n terminal c e Q ω i
    MemLp Y 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, (Y ω)^2 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        ∫ ω, ((upperCellPotentialRepr M n terminal c e ω).ofLp i)^2
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := fun ω => (upperCellPotentialRepr M n terminal c e ω).ofLp i
  let Y := fun ω => upperCellPhysicalPotentialMean M n terminal c e Q ω i
  have hX : MemLp X 2 μ :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).comp_memLp'
      (upper_cell_potential_repr_memLp M n terminal c e)
  have hXm : StronglyMeasurable X :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).continuous.comp_stronglyMeasurable
      (upper_cell_potential_repr_measurable M n terminal c e)
  have hY : MemLp Y 2 μ ∧ lpNorm Y 2 μ ≤ lpNorm X 2 μ :=
    upper_cell_reset_stationary_average_L2 Q hXm hX
  refine ⟨hY.1, ?_⟩
  have hs := hY.2
  rw [upper_cell_reset_lp_two μ Y hY.1.aestronglyMeasurable,
    upper_cell_reset_lp_two μ X hX.aestronglyMeasurable] at hs
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rwa [Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _)),
    Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))] at hsq

/-- The actual mean-vector energy is paid by the exact projected band variance. -/
theorem upper_cell_physical_mean_energy
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) :
    (∫ ω, (∑ i : Fin 2, (upperCellPhysicalPotentialMean M n terminal c e Q ω i)^2)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
    ‖-stationaryPotentialProjection (upperCellResetBandForcing M n terminal c e)‖^2 := by
  have hi (i) := upper_cell_physical_mean_coordinate_energy M n terminal c e Q i
  rw [integral_finsetSum _ (fun i _ =>
    (memLp_two_iff_integrable_sq (hi i).1.aestronglyMeasurable).mp (hi i).1)]
  exact (Finset.sum_le_sum (fun i _ => (hi i).2)).trans_eq
    (upper_cell_physical_coordinate_energy M n terminal c e)

end
end ASDExplicitGamma.Scalar
