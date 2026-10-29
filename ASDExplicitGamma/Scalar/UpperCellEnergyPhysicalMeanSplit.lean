module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalBandSplit
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetLoad
public import ASDExplicitGamma.Scalar.UpperCellEnergyPrincipalGauge

/-! The canonical physical cell mean and its exact constant-skew gauge. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Response Variational Inverse
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open scoped ENNReal
noncomputable section

/-- Mean of the literal flux equals the scalar band's mean skew forcing
plus the physical potential mean, on one event for every coordinate. -/
theorem upper_cell_physical_flux_mean_split
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (fun i => cubeAverage Q (fun x => (realize (cutoffBandFlux M n terminal c e) ω x).ofLp i)) =
        cubeAverage Q (laterScalarBand n terminal (fun _ => c) ω) •
          matVecMul responsePlanarJ e + upperCellPhysicalPotentialMean M n terminal c e Q ω := by
  let finitePhysicalCell : IsFiniteMeasure (volume.restrict (cubeSet Q)) :=
    ⟨by simpa using volume_cubeSet_lt_top Q⟩
  have hj := ae_memLp_two_realize (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (volume_cubeSet_lt_top Q).ne (stronglyMeasurable_cutoffBandFlux M n terminal c e)
    (memLp_two_cutoffBandFlux M n terminal c e)
  have hw := ae_memLp_two_realize (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (volume_cubeSet_lt_top Q).ne (upper_cell_potential_repr_measurable M n terminal c e)
    (upper_cell_potential_repr_memLp M n terminal c e)
  filter_upwards [hj,hw] with ω hj hw
  funext i
  let pr := PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i
  have hji : Integrable (fun x => (realize (cutoffBandFlux M n terminal c e) ω x).ofLp i)
      (volume.restrict (cubeSet Q)) := (pr.comp_memLp' hj).integrable (by norm_num)
  have hwi : Integrable (fun x => (realize (upperCellPotentialRepr M n terminal c e) ω x).ofLp i)
      (volume.restrict (cubeSet Q)) := (pr.comp_memLp' hw).integrable (by norm_num)
  have hraw : Integrable (fun x => laterScalarBand n terminal (fun _ => c) ω x *
      matVecMul responsePlanarJ e i) (volume.restrict (cubeSet Q)) := by
    apply (hji.sub hwi).congr
    filter_upwards with x
    simp only [Pi.sub_apply]
    rw [upper_cell_physical_flux_coordinate_split]
    exact add_sub_cancel_right _ _
  change cubeAverage Q (fun x => (realize (cutoffBandFlux M n terminal c e) ω x).ofLp i) =
    cubeAverage Q (laterScalarBand n terminal (fun _ => c) ω) * matVecMul responsePlanarJ e i +
      cubeAverage Q (fun x => (realize (upperCellPotentialRepr M n terminal c e) ω x).ofLp i)
  simp_rw [upper_cell_physical_flux_coordinate_split]
  unfold cubeAverage
  rw [integral_add hraw hwi,integral_mul_const]
  ring

/-- The actual measurable load lift has the source's exact gauged mean.
The only representation premise is the previously proved literal AE load lift. -/
theorem upper_cell_canonical_gauged_mean
    (M : ABKModel 2) (n terminal : ℤ) (sigma : ℝ) (e : Vec 2) (Q : TriadicCube 2)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q))
    (hF : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∃ hω : MemBlockL2 (openCubeSet Q) (bandLoad M n terminal sigma e ω),
        F ω = toHilbertBlockL2OfBlockField hω) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      constantSkewLoad (cubeAverage Q (laterScalarBand n terminal (fun _ => sigma⁻¹) ω))
        (upperCellResetMeanValue Q (F ω)) =
          (e,upperCellPhysicalPotentialMean M n terminal sigma⁻¹ e Q ω) := by
  filter_upwards [hF,upper_cell_physical_flux_mean_split M n terminal sigma⁻¹ e Q]
    with ω hω hs
  obtain ⟨hω,hωeq⟩ := hω
  have hrep : F ω =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => HilbertBlockVec.ofBlockVec (bandLoad M n terminal sigma e ω x) := by
    rw [hωeq]
    exact coeFn_toHilbertBlockL2OfBlockField hω
  have ht := upper_cell_reset_mean_top Q e (bandLoad M n terminal sigma e ω)
    (fun _ => rfl) (F ω) hrep
  have hb : (upperCellResetMeanValue Q (F ω)).2 =
      cubeAverage Q (laterScalarBand n terminal (fun _ => sigma⁻¹) ω) • matVecMul responsePlanarJ e +
        upperCellPhysicalPotentialMean M n terminal sigma⁻¹ e Q ω := by
    rw [←hs]
    funext i
    exact upper_cell_reset_mean_of_ae_field Q (F ω) _ hrep (.inr i)
  have heq : upperCellResetMeanValue Q (F ω) =
      (e,cubeAverage Q (laterScalarBand n terminal (fun _ => sigma⁻¹) ω) • matVecMul responsePlanarJ e +
        upperCellPhysicalPotentialMean M n terminal sigma⁻¹ e Q ω) := Prod.ext ht hb
  rw [heq,upper_cell_gauged_upper_load]

end
end ASDExplicitGamma.Scalar
