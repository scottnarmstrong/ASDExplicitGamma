module

public import ASDExplicitGamma.Inverse.BankOnePassLocal
public import ASDExplicitGamma.Inverse.BankOnePassMeanActual
public import ASDExplicitGamma.Inverse.FullResponseAttenuatedBank
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Inverse.RawShellBankMoment
public import ASDExplicitGamma.Gaussian.ShellBracket
public import ASDExplicitGamma.Inverse.BankOnePassHeat
public import ASDExplicitGamma.Inverse.AnchorAdapter
public import ASDExplicitGamma.Gaussian.ModelHeatResponse

/-! Concrete local and full-response bank inputs for a one-shell raw-trace
insertion at its fixed base frame. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped ENNReal

/-- The exact local-inverse bank on the source roots of the one-pass insertion. -/
theorem raw_shell_local_inverse_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    InverseBankConclusion M .localInverse (bankLocalRoots (originCube 2 n) 5)
      n (n + 40) (bankPartialInsertionWeights n s t) := by
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hg n hpast).2
  have hgeometry := bank_one_pass_local_geometry n
  exact local_inverse_bank M h hM hg (bankLocalRoots (originCube 2 n) 5)
    n (n + 40) (by omega) (bankPartialInsertionWeights n s t)
    (fun i _ => bank_partial_insertion_weights_bounds n s t ht.2 i)
    hgeometry.1 hgeometry.2 hpast hmean

end ASDExplicitGamma.Inverse
