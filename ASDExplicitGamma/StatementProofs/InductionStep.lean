module

public import ASDExplicitGamma.Joint.StepAssembly
public import ASDExplicitGamma.Joint.Strong20N
public import ASDExplicitGamma.Joint.Root20N
public import ASDExplicitGamma.Joint.Buffer40HistoryN
public import ASDExplicitGamma.Joint.Buffer40MeanN
public import ASDExplicitGamma.Joint.OrdinaryMeanN
public import ASDExplicitGamma.Joint.LowerScalarCoordinates
public import ASDExplicitGamma.Joint.UpperScalarCoordinate
public import ASDExplicitGamma.Native.ThetaScaledReturn
public import ASDExplicitGamma.Joint.LowerScalarNClosed

/-!
# Proof of `ASDExplicitGamma.induction_step`

The induction step: if the native induction state holds below scale `N`, it holds at `N`.
The statement is in `ASDExplicitGamma/Statements/InductionStep.lean`; the proof is assembled here, as
`ASDExplicitGamma.StatementProofs.induction_step`, from proved lemmas.
-/

@[expose] public section

namespace ASDExplicitGamma.StatementProofs

open Algsuperdiff.Section3
open scoped ENNReal

/-- End-to-end conditional step. Its explicit premises are the named
outputs of its component steps: the exact eight-coordinate NA-THETA-SCALING conclusion, the
exact MA ordinary-mean bound, the lower corridor, and the long-block
trial, together with the induction hypothesis. It does not take the seven
assembled components as hypotheses. -/
theorem induction_step_of_producers
    {M : ABKModel 2} {h : ℝ} {N : ℤ}
    (hM : PlanarQ3Gaussian M h := by assumption)
    (hγ : M.gamma ≤ gammaZero := by assumption)
    (hprev : ∀ k : ℤ, k < N → nativeInductionState M h k := by assumption)
    (hscale : ASDExplicitGamma.Native.NativeThetaScaledReturns M N := by assumption)
    (hordinary : ordinaryMean M N ≤ ENNReal.ofReal (3 / 50 * theta M) := by assumption)
    (hcorridor : M.nu ≤ (Annealed.sigmaBar M N : ℝ) ∧
      (31 / 50) * shellVarianceSum h M.gamma N + (19 / 50) * M.nu ^ 2 ≤
        (Annealed.sigmaBar M N : ℝ) ^ 2 := by assumption)
    (htrial : ASDExplicitGamma.Joint.NativeLongBlockTrialConclusion M h N := by assumption)
    : nativeInductionState M h N := by
  have hstep := ASDExplicitGamma.Native.native_step_of_named_producer_outputs
    M N hscale
  have hOrdinary := ASDExplicitGamma.Joint.ordinary_mean_n_of_main_return M N hordinary
  have hStrong := ASDExplicitGamma.Joint.strong20_n_of_native_step M N hstep
  have hRoot := ASDExplicitGamma.Joint.root20_n_of_native_step M N hstep
  have hBufferHistory :=
    ASDExplicitGamma.Joint.buffer40_history_n_of_native_step M N hstep
  have hBufferMean := ASDExplicitGamma.Joint.buffer40_mean_n_of_native_step M N hstep
  have hLower := ASDExplicitGamma.Joint.lower_scalar_n_of_corridor M h N hcorridor
  have hUpper := ASDExplicitGamma.Joint.upper_scalar_n_of_longblock_trial
    M h hM hγ N (fun k hk => hprev k hk) htrial
  exact ASDExplicitGamma.Joint.step_assembly_of_components M h N
    hOrdinary hStrong hRoot hBufferHistory hBufferMean hLower hUpper

/-- **GATE-STEP.** The induction step: the
lower scalar coordinate from JO-LOWER-SCALAR-N (`jo_lower_scalar_N_closed`) and the main
θ-return (`ma_theta_return_real`), assembled by `Joint.gate_step_of_lower_scalar`. -/
theorem induction_step {M : ABKModel 2} {h : ℝ} {N : ℤ}
    (hM : PlanarQ3Gaussian M h := by assumption) (hγ : M.gamma ≤ gammaZero := by assumption)
    (hprev : ∀ n : ℤ, n < N → nativeInductionState M h n := by assumption) :
    nativeInductionState M h N :=
  ASDExplicitGamma.Joint.gate_step_closed M h hM hγ N hprev

end ASDExplicitGamma.StatementProofs
