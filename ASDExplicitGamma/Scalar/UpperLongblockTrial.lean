module

public import ASDExplicitGamma.Scalar.UpperCellEnergyFinal
public import ASDExplicitGamma.Scalar.LongblockTrial

/-! SC-LONGBLOCK-TRIAL: the actual cell estimate inserted into the
no-loss scalar implication, under the standing outer-target chronology. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The physical long-block ratio uses precisely the actual error paid in
the cell theorem. No cell-energy or source estimate is assumed. -/
theorem scalar_upper_longblock_trial
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k<N, nativeInductionState M h k) (n : ℤ) (hn : n<N) :
    let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
    let sigma := (Annealed.sigmaBar M n:ℝ)
    let z := (shellVarianceSum h M.gamma (n+height)-shellVarianceSum h M.gamma n)/(2*sigma^2)
    let err := upperCellErrorProfile M.gamma (M.gamma*(height:ℝ))
    err < 681/10000 ∧ (Annealed.sigmaBar M (n+height):ℝ) ≤ sigma*(1+z+err) := by
  obtain ⟨herr,C,hC,hI,hB⟩ := scalar_upper_cell_energy M h hM hg N hpast n hn
    Model.planarBasis0_unit
  have he : vecDot Model.planarBasis0 Model.planarBasis0 = 1 := by
    have hh := Book.Ch02.vecNorm_sq_eq_vecNormSq Model.planarBasis0
    rw [Model.planarBasis0_unit] at hh
    simpa only [one_pow,vecNormSq] using hh.symm
  have hnT : n < n+(⌊(17/50:ℝ)/M.gamma⌋.toNat:ℤ) := by
    have hh := upper_cell_source_height_pos M hg
    omega
  exact ⟨herr,scalar_longblock_trial_of_cell_energy_bound M h hM hg n _ hnT M.nu_pos
    _ _ Model.planarBasis0 he C (Filter.Eventually.of_forall hC) hI hB⟩

/-- The certified endpoint form consumed by the target-label upper step. -/
theorem scalar_upper_longblock_endpoint
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k<N, nativeInductionState M h k) (n : ℤ) (hn : n<N) :
    let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
    let sigma := (Annealed.sigmaBar M n:ℝ)
    let z := (shellVarianceSum h M.gamma (n+height)-shellVarianceSum h M.gamma n)/(2*sigma^2)
    (Annealed.sigmaBar M (n+height):ℝ) ≤ sigma*(1+z+681/10000) := by
  have ht := scalar_upper_longblock_trial M h hM hg N hpast n hn
  exact ht.2.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) ht.1.le)
    (Annealed.sigmaBar M n).property.le)

end
end ASDExplicitGamma.Scalar
