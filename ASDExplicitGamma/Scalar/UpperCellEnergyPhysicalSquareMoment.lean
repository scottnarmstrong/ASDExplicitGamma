module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalIndependence
public import ASDExplicitGamma.Scalar.UpperCellEnergyPotentialSignal
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetStationaryAverage

/-! Sharp moments of the literal spatial mean in the physical principal load. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
noncomputable section

/-- Coordinate energies of the literal potential representative sum to the
exact stationary projected energy, with no dimension factor. -/
theorem upper_cell_physical_coordinate_energy
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) :
    (∑ i : Fin 2, ∫ ω, ((upperCellPotentialRepr M n terminal c e ω).ofLp i)^2
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
    ‖-stationaryPotentialProjection (upperCellResetBandForcing M n terminal c e)‖^2 := by
  have hm := upper_cell_potential_repr_memLp M n terminal c e
  have hc (i : Fin 2) : MemLp
      (fun ω => (upperCellPotentialRepr M n terminal c e ω).ofLp i) 2
      (Cutoff.cutoffSampleLaw M).toMeasure :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).comp_memLp' hm
  rw [← integral_finset_sum _ (fun i _ =>
    (memLp_two_iff_integrable_sq (hc i).aestronglyMeasurable).mp (hc i))]
  have heq (ω : Cutoff.CutoffSample 2) :
      (∑ i : Fin 2, ((upperCellPotentialRepr M n terminal c e ω).ofLp i)^2) =
        ‖upperCellPotentialRepr M n terminal c e ω‖^2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  simp_rw [heq]
  rw [integral_normSq_eq_norm_sq_toLp hm, upper_cell_potential_repr_class]

/-- Physical Jensen and the stationary Gaussian-square payment give the sharp
L2 bound for the sum of squared actual potential means. -/
theorem upper_cell_physical_square_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) :
    let S := fun ω => ∑ i : Fin 2,
      (upperCellPhysicalPotentialMean M n (n+height) c e Q ω i)^2
    MemLp S 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm S 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ Real.sqrt 3 *
        ‖-stationaryPotentialProjection (upperCellResetBandForcing M n (n+height) c e)‖^2 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := fun i : Fin 2 => fun ω => (upperCellPotentialRepr M n (n+height) c e ω).ofLp i
  let S := fun ω => ∑ i : Fin 2, (upperCellPhysicalPotentialMean M n (n+height) c e Q ω i)^2
  let B := fun ω => ∑ i : Fin 2, cubeAverage Q (fun x => (realize (X i) ω x)^2)
  have hg (i) := upper_cell_potential_repr_centered M h hM n height c e i
  have hb := upper_cell_reset_gaussian_spatial_vector_L2 Q X
    (fun i => (hg i).1) (fun i => (hg i).2.1) (fun i => (hg i).2.2)
  have hSm : StronglyMeasurable S := (Finset.measurable_sum _ (fun i _ =>
    (upper_cell_physical_potential_mean_measurable M n (n+height) c e Q i).measurable.pow_const 2)).stronglyMeasurable
  have hS0 (ω) : 0 ≤ S ω := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB0 (ω) : 0 ≤ B ω := Finset.sum_nonneg (fun i _ => by
    unfold cubeAverage
    exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos Q).le)
      (integral_nonneg (fun _ => sq_nonneg _)))
  have hj : ∀ᵐ ω ∂μ, S ω ≤ B ω :=
    upper_cell_physical_potential_mean_jensen M n (n+height) c e Q
  have hnorm : ∀ᵐ ω ∂μ, ‖S ω‖ ≤ ‖B ω‖ := hj.mono (fun ω hh => by
    rwa [Real.norm_of_nonneg (hS0 ω), Real.norm_of_nonneg (hB0 ω)])
  refine ⟨hb.1.mono hSm.aestronglyMeasurable hnorm, ?_⟩
  have hn : lpNorm S 2 μ ≤ lpNorm B 2 μ := by
    rw [←toReal_eLpNorm, ←toReal_eLpNorm]
    exact ENNReal.toReal_mono hb.1.eLpNorm_ne_top
      (eLpNorm_mono_ae hSm.aestronglyMeasurable hnorm)
  have he := upper_cell_physical_coordinate_energy M n (n+height) c e
  exact hn.trans (hb.2.trans_eq (congrArg (fun x : ℝ => Real.sqrt 3*x) he))

end
end ASDExplicitGamma.Scalar
