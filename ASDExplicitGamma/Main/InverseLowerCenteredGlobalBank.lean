module

public import ASDExplicitGamma.Inverse.BankGlobal

/-! The exact local history set for each insertion shell is also a valid global bank. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization ASDExplicitGamma.Inverse ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Model
open Algsuperdiff.Section3

/-- Each source shell's local-root maximum carries the global bank's
finiteness and L128 history cap. The bank uses the exact local root set and
partial-insertion weights from the all-shell generator row. -/
theorem main_local_history_global_bank_of_native_state
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    InverseBankConclusion M .globalInverse (bankLocalRoots (originCube 2 n) 5)
      n (n + 40) (bankPartialInsertionWeights n s t) := by
  have hgeometry := bank_local_roots_geometry (originCube 2 n) 5 le_rfl
  have hweights : ∀ k ∈ Finset.Ioc n (n + 40),
      0 ≤ bankPartialInsertionWeights n s t k ∧
        bankPartialInsertionWeights n s t k ≤ 1 := by
    intro k _
    exact bank_partial_insertion_weights_bounds n s t ht.2 k
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hg n hpast).1
  exact global_inverse_bank M h hM hg _ n (n + 40) (by omega)
    (bankPartialInsertionWeights n s t) hweights hgeometry.1 hgeometry.2 hpast hmean

/-- First-shell specialization of the all-shell local global-bank adapter. -/
theorem main_first_shell_local_history_global_bank_of_native_state
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    InverseBankConclusion M .globalInverse (bankLocalRoots (originCube 2 n) 5)
      n (n + 40) (bankPartialInsertionWeights n 1 t) :=
  main_local_history_global_bank_of_native_state M h hM hg n 1 t ht hpast

end ASDExplicitGamma.Main
