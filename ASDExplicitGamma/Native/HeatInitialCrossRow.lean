module

public import ASDExplicitGamma.Native.HeatInitialCrossTypeTwo
public import ASDExplicitGamma.Numerics.Native.HeatCross02
public import ASDExplicitGamma.Numerics.Native.HeatCross03
public import ASDExplicitGamma.Numerics.Native.HeatCross04
public import ASDExplicitGamma.Numerics.Native.HeatCross05
public import ASDExplicitGamma.Numerics.Native.HeatCross06
public import ASDExplicitGamma.Numerics.Native.HeatCross07
public import ASDExplicitGamma.Numerics.Native.HeatCross08
public import ASDExplicitGamma.Numerics.Native.HeatCross09
public import ASDExplicitGamma.Numerics.Native.HeatCross10
public import ASDExplicitGamma.Numerics.Native.HeatCross11
public import ASDExplicitGamma.Numerics.Native.HeatCross12
public import ASDExplicitGamma.Numerics.Native.HeatCross13
public import ASDExplicitGamma.Numerics.Native.HeatCross14
public import ASDExplicitGamma.Numerics.Native.HeatCross15
public import ASDExplicitGamma.Numerics.Native.HeatCross16
public import ASDExplicitGamma.Numerics.Native.HeatCross17
public import ASDExplicitGamma.Numerics.Native.HeatCross18
public import ASDExplicitGamma.Numerics.Native.HeatCross19
public import ASDExplicitGamma.Numerics.Native.HeatCross20
public import ASDExplicitGamma.Model.CutoffAction
public import ASDExplicitGamma.Scalar.LawShiftCarrier

/-! The state-driven old/fresh adapter fits the literal source cross row once
the fresh q3 vector's RMS moment is supplied. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Variational
open scoped ENNReal BigOperators

/-- Spatial translation and exact scale shift together preserve the cutoff
sample law. This transports canonical grid moments to the descendants of any
triadic parent cube. -/
theorem nativeHeat_cutoff_lintegral_translate_scale_shift
    (M : ABKModel 2) (z : Vec 2) (n : ℤ)
    (f : Cutoff.CutoffSample 2 → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ ω, f (ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma n
      (Cutoff.translateCutoffSample z ω))
      ∂(Cutoff.cutoffSampleLaw M).toMeasure =
    ∫⁻ ω, f ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  let T : Cutoff.CutoffSample 2 → Cutoff.CutoffSample 2 := fun ω =>
    ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma n
      (Cutoff.translateCutoffSample z ω)
  have hT : Measurable T :=
    ASDExplicitGamma.Scalar.measurable_cutoff_scale_shift M.gamma n |>.comp
      (Cutoff.measurable_translateCutoffSample z)
  have hlaw : Measure.map T (Cutoff.cutoffSampleLaw M).toMeasure =
      (Cutoff.cutoffSampleLaw M).toMeasure := by
    rw [show T = ASDExplicitGamma.Scalar.cutoffScaleShift M.gamma n ∘
        Cutoff.translateCutoffSample z by rfl,
      ← Measure.map_map
        (ASDExplicitGamma.Scalar.measurable_cutoff_scale_shift M.gamma n)
        (Cutoff.measurable_translateCutoffSample z),
      Cutoff.map_translateCutoffSample_cutoffSampleLaw,
      ASDExplicitGamma.Scalar.cutoff_scale_shift_preserves_law]
  calc
    ∫⁻ ω, f (T ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure =
        ∫⁻ y, f y ∂Measure.map T (Cutoff.cutoffSampleLaw M).toMeasure :=
      (MeasureTheory.lintegral_map hf hT).symm
    _ = ∫⁻ ω, f ω ∂(Cutoff.cutoffSampleLaw M).toMeasure := by rw [hlaw]

end ASDExplicitGamma.Native
