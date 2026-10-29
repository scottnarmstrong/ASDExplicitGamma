module

public import ASDExplicitGamma.Statements.MolecularEntrance
public import ASDExplicitGamma.Statements.AllorderOfState
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Statements.GammaZero
public import ASDExplicitGamma.Statements.PlanarQ3Gaussian
public import ASDExplicitGamma.Statements.ShellVarianceSum
public import ASDExplicitGamma.Statements.AllOrderBounds
public import ASDExplicitGamma.Statements.InductionStep

/-!
# Proof of `ASDExplicitGamma.explicit_induction_bounds`

The explicit induction bounds follow by strong induction on the scale, the step being the induction-step theorem.
The statement is in `ASDExplicitGamma/Statements/ExplicitInductionBounds.lean`; the proof is assembled here, as
`ASDExplicitGamma.StatementProofs.explicit_induction_bounds`, from proved lemmas.
-/


@[expose] public section

namespace ASDExplicitGamma.StatementProofs

open Algsuperdiff.Section3

/-- Strong induction over `ℤ` from the molecular-entrance half-line: the native state at every label. -/
theorem nativeInductionState_all_of_step (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ 17 / 50000)
    (hstep : ∀ N : ℤ, (∀ n : ℤ, n < N → nativeInductionState M h n) → nativeInductionState M h N) :
    ∀ m : ℤ, nativeInductionState M h m := by
  obtain ⟨K, hK⟩ := molecular_entrance (M := M) (h := h) (hM := hM) (hγ := by simpa [gammaZero] using hγ)
  -- claim: state holds for all n ≤ K + j, by induction on j
  have key : ∀ j : ℕ, ∀ n : ℤ, n ≤ K + j → nativeInductionState M h n := by
    intro j
    induction j with
    | zero => intro n hn; exact hK n (by simpa using hn)
    | succ j ih =>
      intro n hn
      exact hstep n (fun k hk => ih k (by push_cast at hn; omega))
  intro m
  exact key (Int.toNat (m - K)) m (by omega)

/-- ROOT-T1 from the induction-step statement as a binder. -/
theorem explicit_induction_bounds_of_step (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ 17 / 50000)
    (hstep : ∀ N : ℤ, (∀ n : ℤ, n < N → nativeInductionState M h n) → nativeInductionState M h N)
    (m : ℤ) :
    M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
    (31 / 50) * shellVarianceSum h M.gamma m + (19 / 50) * M.nu ^ 2 ≤
      (Annealed.sigmaBar M m : ℝ) ^ 2 ∧
    (Annealed.sigmaBar M m : ℝ) ^ 2 ≤ M.nu ^ 2 + (13 / 8) * shellVarianceSum h M.gamma m ∧
    AllOrderBounds M m := by
  have hall := nativeInductionState_all_of_step M h hM hγ hstep
  obtain ⟨-, -, -, -, -, h6, h7, h8⟩ := hall m
  exact ⟨h6, h7, h8, allorder_of_state (M := M) (h := h) (hM := hM) (hγ := by simpa [gammaZero] using hγ) (hstate := hall) (m := m)⟩

/-- **ROOT-T1.** The explicit induction bounds: the GATE-STEP theorem `induction_step` supplies the step of the strong induction. -/
theorem explicit_induction_bounds {M : ABKModel 2} {h : ℝ}
    (hM : PlanarQ3Gaussian M h := by assumption) (hγ : M.gamma ≤ 17 / 50000 := by assumption)
    {m : ℤ} :
    M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
    (31 / 50) * shellVarianceSum h M.gamma m + (19 / 50) * M.nu ^ 2 ≤
      (Annealed.sigmaBar M m : ℝ) ^ 2 ∧
    (Annealed.sigmaBar M m : ℝ) ^ 2 ≤ M.nu ^ 2 + (13 / 8) * shellVarianceSum h M.gamma m ∧
    AllOrderBounds M m :=
  explicit_induction_bounds_of_step M h hM hγ
    (fun N hprev => ASDExplicitGamma.induction_step M h hM (by simpa [gammaZero] using hγ) N hprev) m

end ASDExplicitGamma.StatementProofs
