module

public import ASDExplicitGamma.Native.HeatVHEATSourceRow
public import ASDExplicitGamma.Native.GenericSourceBandCoefficientBudget
public import ASDExplicitGamma.Native.GenericSourceBandHistory
public import ASDExplicitGamma.Native.GenericSourceShellRoot

/-! All-degree shell-generator control for the actual simultaneous source
band, before taking the source-law expectation. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Response
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped ENNReal

noncomputable section

/-- The finite source-band sum of q3 power generators at degree `k`. -/
def nativeSourceBandPowerGeneratorK (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (height : ℕ) (t : ℝ) (k : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i : Fin height,
    modelPowerHeatGenerator (modelTraceObservable n M.nu (Annealed.sigmaBar M n))
      (pureFluxMainCubeQ3Directions n
        (q3ModelAmplitude M h (n + ((i.val + 1 : ℕ) : ℤ)))
        (q3ModelLength (n + ((i.val + 1 : ℕ) : ℤ))))
      (k : ℝ) (nativeSourceBandScalar n height t ω)

end
end ASDExplicitGamma.Native
end
