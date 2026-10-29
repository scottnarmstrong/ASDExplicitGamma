module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPotentialVariance

/-! The actual physical potential-correction representative, retaining the exact
pointwise splitting of the full flux into raw forcing and correction. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Frozen.Assumptions
noncomputable section

/-- The same shell-sum corrector representative used inside the genuine flux. -/
def upperCellPotentialRepr (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) : HilbertVec 2 :=
  shellSumCorrectorRepr M (c • e) n terminal (shellSumValuePath n terminal ω.val)

/-- Strong measurability holds for the literal physical representative. -/
theorem upper_cell_potential_repr_measurable
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) :
    StronglyMeasurable (upperCellPotentialRepr M n terminal c e) :=
  (stronglyMeasurable_shellSumCorrectorRepr M (c • e) n terminal).comp_measurable
    (measurePreserving_shellSumValuePath_cutoffSample M n terminal).measurable

/-- Square integrability comes from the actual stationary corrector construction. -/
theorem upper_cell_potential_repr_memLp
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) :
    MemLp (upperCellPotentialRepr M n terminal c e) 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
  (memLp_two_shellSumCorrectorRepr M (c • e) n terminal).comp_measurePreserving
    (measurePreserving_shellSumValuePath_cutoffSample M n terminal)

/-- The physical representative is exactly the source-sign potential projection
whose Gaussian law and sharp variance were proved on the cutoff carrier. -/
theorem upper_cell_potential_repr_class
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) :
    (upper_cell_potential_repr_memLp M n terminal c e).toLp
      (upperCellPotentialRepr M n terminal c e) =
      -stationaryPotentialProjection (upperCellResetBandForcing M n terminal c e) := by
  let hp := measurePreserving_shellSumValuePath_cutoffSample M n terminal
  have hequiv (x : Vec 2) (ω : Cutoff.CutoffSample 2) :
      shellSumValuePath n terminal (x +ᵥ ω).val = x +ᵥ shellSumValuePath n terminal ω.val :=
    shellSumValuePath_translateSequence n terminal x ω.val
  change carrierTransport (HilbertVec 2) hp
    ((memLp_two_shellSumCorrectorRepr M (c • e) n terminal).toLp
      (shellSumCorrectorRepr M (c • e) n terminal)) = _
  rw [toLp_shellSumCorrectorRepr]
  change carrierTransport (HilbertVec 2) hp
    (-stationaryPotentialProjection (shellSumForcingL2 M (c • e) n terminal)) = _
  rw [map_neg,←stationaryPotentialProjection_carrierTransport hp hequiv]
  rfl

/-- Exact pointwise physical flux splitting; the correction is not replaced
by an arbitrary version or by evaluation at a frozen cell center. -/
theorem upper_cell_physical_flux_split
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    realize (cutoffBandFlux M n terminal c e) ω x =
      valuePathForcing (c • e) (shellSumValuePath n terminal (x +ᵥ ω).val) +
        realize (upperCellPotentialRepr M n terminal c e) ω x := rfl

/-- Coordinate laws of the literal physical representative, rather than just
of an unspecified L2-class representative. -/
theorem upper_cell_potential_repr_gaussian
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (i : Fin 2) :
    ∃ variance : NNReal, (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω => (upperCellPotentialRepr M n (n+height) c e ω).ofLp i) =
        ProbabilityTheory.gaussianReal 0 variance := by
  let X := upperCellPotentialRepr M n (n+height) c e
  have hmem := upper_cell_potential_repr_memLp M n (n+height) c e
  have hc := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).coeFn_compLpL
    (hmem.toLp X)
  have hr := hmem.coeFn_toLp
  change (fun ω => vectorL2Coord i (hmem.toLp X) ω) =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
    (fun ω => (hmem.toLp X ω).ofLp i) at hc
  rw [upper_cell_potential_repr_class] at hc hr
  have ha : (fun ω => vectorL2Coord i (-stationaryPotentialProjection
      (upperCellResetBandForcing M n (n+height) c e)) ω) =ᵐ[(Cutoff.cutoffSampleLaw M).toMeasure]
      (fun ω => (X ω).ofLp i) := by
    filter_upwards [hc,hr] with ω hc hr
    exact hc.trans (congrArg (fun v : HilbertVec 2 => v.ofLp i) hr)
  obtain ⟨v,hv⟩ := upper_cell_physical_potential_gaussian M h hM n height c e i
  exact ⟨v,(Measure.map_congr ha.symm).trans hv⟩

/-- The literal correction coordinates supply all Gaussian-square inputs for
physical spatial averaging, without any premise on the projected field. -/
theorem upper_cell_potential_repr_centered
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (n : ℤ) (height : ℕ) (c : ℝ) (e : Vec 2) (i : Fin 2) :
    let X := fun ω => (upperCellPotentialRepr M n (n+height) c e ω).ofLp i
    StronglyMeasurable X ∧ ProbabilityTheory.HasGaussianLaw X (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, X ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) = 0 := by
  let X := fun ω => (upperCellPotentialRepr M n (n+height) c e ω).ofLp i
  have hm : StronglyMeasurable X :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).continuous.comp_stronglyMeasurable
      (upper_cell_potential_repr_measurable M n (n+height) c e)
  obtain ⟨v,hv⟩ := upper_cell_potential_repr_gaussian M h hM n height c e i
  refine ⟨hm,⟨hm.aemeasurable,by rw [hv]; infer_instance⟩,?_⟩
  calc
    (∫ ω, X ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
        ∫ x : ℝ, x ∂(Cutoff.cutoffSampleLaw M).toMeasure.map X :=
      (integral_map hm.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = 0 := by rw [hv,ProbabilityTheory.integral_id_gaussianReal]

end
end ASDExplicitGamma.Scalar
