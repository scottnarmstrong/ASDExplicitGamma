module

public import ASDExplicitGamma.Scalar.UpperCellEnergyLpLift
public import ASDExplicitGamma.Scalar.TrialIntegrability
public import ASDExplicitGamma.Scalar.UpperCellEnergyMeasurability

/-! The actual full compatible band field as a measurable Hilbert-valued
random load. The construction agrees with the spatial field almost surely. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Response MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The full band load has a measurable L²-valued version on every cell. -/
theorem upper_cell_measurable_band_load
    (M : ABKModel 2) (n N : ℤ) (sigma : ℝ) (e : Vec 2) (Q : TriadicCube 2) :
    ∃ F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q),
      Measurable F ∧
      ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        ∃ hF : MemBlockL2 (openCubeSet Q) (bandLoad M n N sigma e ω),
          F ω = toHilbertBlockL2OfBlockField hF := by
  let finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let : IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance
  let : Fact (1 ≤ (2:ENNReal)) := ⟨by norm_num⟩
  let : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
  let : SecondCountableTopology (HilbertBlockL2 (openCubeSet Q)) := inferInstance
  let X := fun ω => hilbertifyBlockField (bandLoad M n N sigma e ω)
  have hX : Measurable (Function.uncurry X) :=
    (HilbertBlockVec.continuousLinearEquivBlockVec 2).symm.continuous.measurable.comp
      (stronglyMeasurable_bandLoad M n N sigma e).measurable
  obtain ⟨F,hF,hFeq⟩ := upper_cell_measurable_Lp_lift
    (volumeMeasureOn (openCubeSet Q)) X hX
  refine ⟨F,hF,?_⟩
  filter_upwards [ae_memBlockL2_bandLoad M n N sigma e Q] with ω hω
  exact ⟨hω,hFeq ω (memHilbertBlockL2_hilbertifyBlockField hω)⟩

end
end ASDExplicitGamma.Scalar
