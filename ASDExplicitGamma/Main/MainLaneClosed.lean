module

public import ASDExplicitGamma.Main.ThetaGeneratorReturn
public import ASDExplicitGamma.Main.OrdinaryReturn
public import ASDExplicitGamma.Joint.GateStep

/-! Closed main-range tail: the ordinary-return tail and the GATE-STEP reduction with
`MaThetaReturnReal` discharged by `ma_theta_return_real`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

/-- STEP-MA-ORDINARY-RETURN-LINTEGRAL, closed. -/
theorem step_ma_ordinary_return_lintegral (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ n < N, nativeInductionState M h n) :
    ordinaryMean M N ≤ ENNReal.ofReal (3 / 50 * theta M) ∧ ordinaryMean M N ≠ ∞ ∧
      ordinaryMean M N = ENNReal.ofReal
        (∫ ω, cutoffTraceDefect M N N ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) :=
  step_ma_ordinary_return_lintegral' M N (ma_theta_return M h hM hγ N hpast)

/-- MA-ORDINARY-RETURN, closed. -/
theorem ma_ordinary_return_node' (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ n < N, nativeInductionState M h n) :
    ordinaryMean M N ≤ ENNReal.ofReal (3 / 50 * theta M) :=
  ma_ordinary_return_node M h N (ma_theta_return_real M h hM hγ N) hpast

/-- JO-ORDINARY-MEAN, closed. -/
theorem jo_ordinary_mean' (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ n < N, nativeInductionState M h n) :
    ordinaryMean M N ≤ ENNReal.ofReal (3 / 50 * theta M) :=
  jo_ordinary_mean M h N (ma_theta_return_real M h hM hγ N) hpast

end ASDExplicitGamma.Main

namespace ASDExplicitGamma.Joint

open Algsuperdiff.Section3

/-- GATE-STEP with only JO-LOWER-SCALAR-N left. -/
theorem gate_step_of_lower_scalar (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hprev : ∀ n : ℤ, n < N → nativeInductionState M h n)
    (hLower : LowerScalarConclusion M h N) :
    nativeInductionState M h N :=
  gate_step_of_lower_scalar_and_theta M h hM hγ N hprev hLower
    (ASDExplicitGamma.Main.ma_theta_return_real M h hM hγ N)

end ASDExplicitGamma.Joint
