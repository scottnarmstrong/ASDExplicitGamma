module

public import ASDExplicitGamma.Inverse.BankOnePassMean
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankAdapter

/-! The q3 pure-flux theorem instantiates the one-pass mean inputs. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise

/-- The actual forty-shell true-frame mean, with the pure-flux generator
instantiated from the strict-past native states. -/
theorem bank_one_pass_true_frame_mean_of_states
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (k : ℤ)
    (hpast : ∀ n < k, nativeInductionState M h n)
    (hstate : nativeInductionState M h k) :
    bankCompletedInverseTraceMean k M (k+40) (Annealed.sigmaBar M (k+40):ℝ) <
      2+747/5000 := by
  exact bank_one_pass_true_frame_mean_of_generator M h hM hg k hpast hstate
    (bankPureFluxGeneratorInput M h hM hg k hpast)

/-- The causal H3 input for both inverse banks is available directly from the
native past states and the proved per-shell generator. -/
theorem bank_inverse_mean_inputs_of_states
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m, nativeInductionState M h n) :
    ClippedInverseMeanInput M m .globalInverse ∧
      ClippedInverseMeanInput M m .localInverse := by
  apply bank_inverse_mean_inputs_of_generator M h hM hg m hpast
  intro n hn
  exact bankPureFluxGeneratorInput M h hM hg (n-40) (fun j hj => hpast j (by omega))

end ASDExplicitGamma.Inverse
