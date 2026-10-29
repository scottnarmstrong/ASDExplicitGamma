module

public import ASDExplicitGamma.Main.EnvelopeHTheta
public import ASDExplicitGamma.Main.EnvelopeHSharpEnv

/-! The `hHist` hypothesis of the `*_ofHist` variants, discharged by the
MA-ENVELOPE-H result with `Hfun := mainEnvelopeH35Theta (theta M) (b²) M.gamma`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Inverse

noncomputable section

/-- History envelope at all `s ∈ [0,1]`, states strictly below `N`. -/
theorem hot_hist_N_Th (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ) (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
        (fun s => mainEnvelopeH35Theta (theta M)
          ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma s) s :=
  fun s hs => main_ordinary_trace_max_history_memLp_two_le_mainEnvelopeH35Theta M h hM hγ m
    (fun n hn => hpast n (lt_of_le_of_lt hn hm)) s hs.1 hs.2

end

end ASDExplicitGamma.Main
