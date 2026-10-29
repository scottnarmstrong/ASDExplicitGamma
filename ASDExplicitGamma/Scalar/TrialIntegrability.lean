module

public import ASDExplicitGamma.Scalar.StationaryTrial
public import ASDExplicitGamma.Scalar.CutoffMeasurability
public import Homogenization.CoarseGraining.MuOperator.CoeffOperator

/-! Honest spatial energy integrability of the compatible cell trials. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff Algsuperdiff.Section3.Provider.Corrector

/-- The actual stationary compatible load is locally L² almost surely. -/
theorem ae_memBlockL2_bandLoad (M : ABKModel 2) (n N : ℤ) (σ : ℝ)
    (e : Vec 2) (Q : TriadicCube 2) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      MemBlockL2 (openCubeSet Q) (bandLoad M n N σ e ω) := by
  let finiteBandCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hlocal := ae_memLp_two_realize (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
    (volume_openCubeSet_lt_top Q).ne (stronglyMeasurable_cutoffBandFlux M n N σ⁻¹ e)
    (memLp_two_cutoffBandFlux M n N σ⁻¹ e)
  filter_upwards [hlocal] with ω hω
  have hv : MemVectorL2 (openCubeSet Q)
      (fun x => (realize (cutoffBandFlux M n N σ⁻¹ e) ω x).toVec) :=
    (HilbertVec.continuousLinearEquivVec 2).toContinuousLinearMap.comp_memLp' hω
  have ht : MemBlockL2 (openCubeSet Q) (fun _ : Vec 2 => (e,(0:Vec 2))) := memLp_const _
  have hb := scalar_bottom_load_memL2 hv
  convert ht.add hb using 1
  funext x
  simp [bandLoad, scalarBottomLoad]

/-- Every genuine L² block field has integrable complete energy for the
locally bounded terminal cutoff, in the fixed positive scalar frame. -/
theorem cutoff_energy_density_integrableOn (M : ABKModel 2) (N : ℤ)
    (σ : ℝ) (hσ : 0 < σ) (Q : TriadicCube 2) (ω : CutoffSample 2)
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F) :
    IntegrableOn (fun x => responseFrameEnergyDensity M.nu σ
      (Cutoff.cutoff N ω x 1 0) (F x)) (openCubeSet Q) := by
  let finiteEnergyCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let k := oldCutoffSkewCoefficient N Q ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ k
  have hi := blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn
    (X := blockStateOfField F) hF hEll
  have heq : (fun x => responseFrameEnergyDensity M.nu σ
        (responseCoefficientExtension k x) (F x)) =
      fun x => 2*blockEnergyDensity a (blockStateOfField F) x := by
    funext x
    exact ASDExplicitGamma.Variational.responseFrameEnergyDensity_eq_twice_blockEnergyDensity
      M.nu σ M.nu_pos hσ k (blockStateOfField F) x
  have he : (fun x => responseFrameEnergyDensity M.nu σ
      (Cutoff.cutoff N ω x 1 0) (F x)) =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => 2*blockEnergyDensity a (blockStateOfField F) x := by
    rw [← heq]
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    rw [old_cutoff_skew_coefficient_value N Q ω hx]
  exact (hi.const_mul 2).congr he.symm

end ASDExplicitGamma.Scalar
