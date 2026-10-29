module

public import ASDExplicitGamma.Main.FrameEndpoint
public import ASDExplicitGamma.Main.OrdinaryReturnIntegral

/-! The one-insertion heat endpoint as an ordinary-mean cap. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open scoped ENNReal

/-- A real heat bound in the OLD frame, followed by the exact completed-law
frame restoration ratio, gives the next completed label's ordinary mean cap. -/
theorem main_ordinary_mean_le_of_one_insertion_heat_bound
    (M : ABKModel 2) (m : ℤ) (R C : ℝ)
    (hr : 1 ≤ (Annealed.sigmaBar M (m + 1) : ℝ) /
      (Annealed.sigmaBar M m : ℝ))
    (hR : (Annealed.sigmaBar M (m + 1) : ℝ) /
      (Annealed.sigmaBar M m : ℝ) ≤ R)
    (hheat : modelTraceHeatAverage (m + 1) M m 1 ≤ C) :
    ordinaryMean M (m + 1) ≤ ENNReal.ofReal (R * C) := by
  have hR1 : 1 ≤ R := hr.trans hR
  have hR0 : 0 ≤ R := by linarith
  have hreturn := main_completed_endpoint_return_of_ratio M m (m + 1) R hr hR
  have hreal :
      (∫ ω, cutoffTraceDefect M (m + 1) (m + 1) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ R * C := by
    calc
      _ ≤ R * modelTraceHeatAverage (m + 1) M m 1 := hreturn
      _ ≤ R * C := mul_le_mul_of_nonneg_left hheat hR0
  exact main_ordinary_mean_le_of_real_expectation M (m + 1) hreal

end ASDExplicitGamma.Main
