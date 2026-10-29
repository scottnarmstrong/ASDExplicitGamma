module

public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Model.ShellScaling
public import ASDExplicitGamma.Statements.CutoffTraceDefect

/-! MA-PARTIAL-INSERTION: the actual cutoff law and the deterministic OLD frame. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions

/-- The physical coefficient is exactly the older cutoff plus the fresh shell. -/
theorem mainInsertion_coefficient (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (omega : Cutoff.CutoffSample 2) :
    Model.partialInsertedCoefficient M m t omega =
      Cutoff.coefficientCutoff M.nu m omega + Real.sqrt t • ShellField.forgetShell (omega.1 (m + 1)) := rfl

/-- The old completed law is precisely the frozen cutoff probability law. -/
theorem mainInsertion_old_law (M : ABKModel 2) (m : ℤ) :
    Measure.map (Cutoff.coefficientCutoff M.nu m) (Cutoff.cutoffSampleLaw M).toMeasure =
      Cutoff.coefficientCutoffLaw M m := by
  rw [Cutoff.coefficientCutoffLaw, Cutoff.coefficientCutoffProbabilityLaw, ProbabilityMeasure.toMeasure_map]

/-- The independent product law uses the actual completed coefficient and next q3 shell. -/
theorem mainInsertion_product_law (M : ABKModel 2) (m : ℤ) :
    Measure.map (fun omega : Cutoff.CutoffSample 2 =>
        (Cutoff.coefficientCutoff M.nu m omega, omega.1 (m + 1))) (Cutoff.cutoffSampleLaw M).toMeasure =
      (Cutoff.coefficientCutoffLaw M m).prod
        (Measure.map (ShellField.triadicScale M.gamma (m + 1)) (ShellField.zeroShellLaw M.P).toMeasure) := by
  rw [Model.map_pair_coefficientCutoff_freshShell, mainInsertion_old_law]

/-- The next completed UV series is the old UV series plus the actual next shell. -/
theorem mainInsertion_cutoff_succ (M : ABKModel 2) (m : ℤ)
    (omega : Cutoff.CutoffSample 2) (x : Vec 2) (i j : Fin 2) :
    Cutoff.coefficientCutoff M.nu (m + 1) omega x i j =
      Cutoff.coefficientCutoff M.nu m omega x i j + omega.1 (m + 1) x i j := by
  obtain ⟨ell, hx⟩ := Cutoff.exists_nat_openOriginCube_of_isCompact (K := ({x} : Set (Vec 2))) isCompact_singleton
  have hx' := hx (Set.mem_singleton x)
  have hs : Summable (fun r : ℕ => omega.1 ((m + 1) - (r : ℤ)) x i j) := by
    refine (Cutoff.summable_cutoffLocalControl (ell : ℤ) (m + 1) omega).of_norm_bounded fun r => ?_
    simpa only [Real.norm_eq_abs] using
      Cutoff.abs_entry_le_localCubeControl (ell : ℤ) (omega.1 ((m + 1) - (r : ℤ))) hx' i j
  rw [Model.coefficientCutoff_eq_nu_add_olderField_entry,
    Model.coefficientCutoff_eq_nu_add_olderField_entry]
  have hsum := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, sub_zero] at hsum
  have hindex (r : ℕ) : (m + 1) - ((r + 1 : ℕ) : ℤ) = m - (r : ℤ) := by omega
  simp_rw [hindex] at hsum
  linarith only [hsum]

/-- Time one is the next completed coefficient, still evaluated later in the OLD frame. -/
theorem mainInsertion_coefficient_one (M : ABKModel 2) (m : ℤ) (omega : Cutoff.CutoffSample 2) :
    Model.partialInsertedCoefficient M m 1 omega = Cutoff.coefficientCutoff M.nu (m + 1) omega := by
  ext x i j
  rw [mainInsertion_cutoff_succ]
  simp [Model.partialInsertedCoefficient, RegCoeffField.add_apply, RegCoeffField.smul_apply]

end ASDExplicitGamma.Main
