module

public import ASDExplicitGamma.Main.OrdinaryReturnEndpoint
public import ASDExplicitGamma.Joint.OrdinaryMeanN
public import ASDExplicitGamma.Statements.Theta

/-! STEP-MA-ORDINARY-RETURN-LINTEGRAL, MA-ORDINARY-RETURN and JO-ORDINARY-MEAN on the certificate. MA-THETA-CONTINUATION enters only as the named real-valued return hypothesis
`MaThetaReturnReal`; neither the OLD `mainReturn_certificate` nor any `mainError` is used. -/

@[expose] public section
noncomputable section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open scoped ENNReal

/-- The expected final shape of MA-THETA-CONTINUATION composed with MA-CHRONOLOGY and the cold
start at the target label `N`: the real expectation of the fixed-frame target trace defect is at
most `3θ/50`, given the native states at labels below `N`. -/
def MaThetaReturnReal (M : ABKModel 2) (h : ℝ) (N : ℤ) : Prop :=
  (∀ n < N, nativeInductionState M h n) →
    (∫ ω, cutoffTraceDefect M N N ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      3 / 50 * theta M

/-- STEP-MA-ORDINARY-RETURN-LINTEGRAL: the real expectation bound gives the `ENNReal.ofReal`
cap on the frozen `ordinaryMean`; the lintegral is finite and equals the Bochner expectation
(integrability from the fixed-ν cutoff-law trace theorem). -/
theorem step_ma_ordinary_return_lintegral' (M : ABKModel 2) (N : ℤ)
    (hreal : (∫ ω, cutoffTraceDefect M N N ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      3 / 50 * theta M) :
    ordinaryMean M N ≤ ENNReal.ofReal (3 / 50 * theta M) ∧ ordinaryMean M N ≠ ∞ ∧
      ordinaryMean M N = ENNReal.ofReal
        (∫ ω, cutoffTraceDefect M N N ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) := by
  have hle := main_ordinary_mean_le_of_real_expectation M N hreal
  have hfin : ordinaryMean M N ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hle, hfin, ?_⟩
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hnonneg : 0 ≤ᵐ[μ] cutoffTraceDefect M N N := Filter.Eventually.of_forall fun ω =>
    Variational.cutoffTraceDefect_nonneg M N N ω
  have hmeas : AEStronglyMeasurable (cutoffTraceDefect M N N) μ :=
    (Variational.cutoffTraceDefect_measurable M N N).aestronglyMeasurable
  have hrealEq : (∫ ω, cutoffTraceDefect M N N ω ∂μ) = (ordinaryMean M N).toReal := by
    simpa only [ordinaryMean, μ] using (integral_eq_lintegral_of_nonneg_ae hnonneg hmeas)
  rw [hrealEq, ENNReal.ofReal_toReal hfin]

/-- MA-ORDINARY-RETURN on the certificate, from the named MA-THETA-CONTINUATION return. -/
theorem ma_ordinary_return_node (M : ABKModel 2) (h : ℝ) (N : ℤ)
    (hθ : MaThetaReturnReal M h N) (hpast : ∀ n < N, nativeInductionState M h n) :
    ordinaryMean M N ≤ ENNReal.ofReal (3 / 50 * theta M) :=
  (step_ma_ordinary_return_lintegral' M N (hθ hpast)).1

/-- JO-ORDINARY-MEAN: the joint adapter applied to MA-ORDINARY-RETURN. -/
theorem jo_ordinary_mean (M : ABKModel 2) (h : ℝ) (N : ℤ)
    (hθ : MaThetaReturnReal M h N) (hpast : ∀ n < N, nativeInductionState M h n) :
    ordinaryMean M N ≤ ENNReal.ofReal (3 / 50 * theta M) :=
  ASDExplicitGamma.Joint.ordinary_mean_n_of_main_return M N
    (ma_ordinary_return_node M h N hθ hpast)

end ASDExplicitGamma.Main

end
