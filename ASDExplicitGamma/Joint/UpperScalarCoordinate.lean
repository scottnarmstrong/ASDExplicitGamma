module

public import ASDExplicitGamma.Scalar.UpperStep
public import ASDExplicitGamma.Numerics.Scalar.Upper

/-! The target upper scalar coordinate from the long-block trial producer. -/

@[expose] public section

namespace ASDExplicitGamma.Joint

open Homogenization Algsuperdiff.Section3

/-- Exact SC-LONGBLOCK-TRIAL output, with its actual error represented by the
source expression certified in NU-SC-UPPER-ERROR. -/
def NativeLongBlockTrialConclusion (M : ABKModel 2) (h : ℝ) (N : ℤ) : Prop :=
  let n : ℤ := N - ⌊(17 / 50 : ℝ) / M.gamma⌋
  (Annealed.sigmaBar M N : ℝ) ≤
    (Annealed.sigmaBar M n : ℝ) *
      (1 + (shellVarianceSum h M.gamma N - shellVarianceSum h M.gamma n) /
        (2 * (Annealed.sigmaBar M n : ℝ) ^ 2) +
        ASDExplicitGamma.Numerics.Mirror.evalReal
          ASDExplicitGamma.Numerics.Scalar.scalarRealEnv
          ASDExplicitGamma.Numerics.Scalar.upperErrorExpr)

/-- Apply the fixed-target upper-step adapter to the exact long-block trial
conclusion, with only the strict-past native states. -/
theorem upper_scalar_n_of_longblock_trial
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hprev : ∀ k < N, nativeInductionState M h k)
    (htrial : NativeLongBlockTrialConclusion M h N) :
    (Annealed.sigmaBar M N : ℝ) ^ 2 ≤
      M.nu ^ 2 + (13 / 8 : ℝ) * shellVarianceSum h M.gamma N := by
  let n : ℤ := N - ⌊(17 / 50 : ℝ) / M.gamma⌋
  let z : ℝ := (shellVarianceSum h M.gamma N - shellVarianceSum h M.gamma n) /
    (2 * (Annealed.sigmaBar M n : ℝ) ^ 2)
  have hσn : 0 < (Annealed.sigmaBar M n : ℝ) :=
    (Annealed.sigmaBar_characterization M n).1
  have htrialExact : (Annealed.sigmaBar M N : ℝ) ≤
      (Annealed.sigmaBar M n : ℝ) *
        (1 + z + ASDExplicitGamma.Numerics.Mirror.evalReal
          ASDExplicitGamma.Numerics.Scalar.scalarRealEnv
          ASDExplicitGamma.Numerics.Scalar.upperErrorExpr) := by
    simpa [NativeLongBlockTrialConclusion, n, z, add_assoc] using htrial
  have htrialFixed : (Annealed.sigmaBar M N : ℝ) ≤
      (Annealed.sigmaBar M n : ℝ) * (1 + z + (681 / 10000 : ℝ)) := by
    calc
      (Annealed.sigmaBar M N : ℝ) ≤
          (Annealed.sigmaBar M n : ℝ) *
            (1 + z + ASDExplicitGamma.Numerics.Mirror.evalReal
              ASDExplicitGamma.Numerics.Scalar.scalarRealEnv
              ASDExplicitGamma.Numerics.Scalar.upperErrorExpr) := htrialExact
      _ ≤ (Annealed.sigmaBar M n : ℝ) * (1 + z + (681 / 10000 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (by linarith [ASDExplicitGamma.Numerics.Scalar.upper_error_bounds.1])
          hσn.le
  exact ASDExplicitGamma.Scalar.scalar_upper_step_of_longblock_trial
    M h hM hγ N hprev htrialFixed

end ASDExplicitGamma.Joint
