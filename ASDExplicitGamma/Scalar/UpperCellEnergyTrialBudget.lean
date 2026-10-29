module

public import ASDExplicitGamma.Scalar.UpperCellEnergyTrialTransfer
public import ASDExplicitGamma.Scalar.UpperCellEnergyBudgetAssembly

/-! Final trial assembly, with the separately owned physical RESET payment
kept explicit until its producer is available. This is not the node export. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Algsuperdiff.Section3
noncomputable section

/-- Assemble the source cell trial from the proved principal payment and the
actual RESET first moment for the same F. The sole remaining estimate premise
is explicitly named hreset and must be discharged by the caller. -/
theorem upper_cell_trial_budget_of_reset
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (n : ℤ) (hn : n<N)
    {e : Vec 2} (he : Book.Ch02.vecNorm e = 1)
    (F : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet (originCube 2 (n-14))))
    (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∃ hω : MemBlockL2 (openCubeSet (originCube 2 (n-14)))
        (bandLoad M n (n+⌊(17/50:ℝ)/M.gamma⌋.toNat) (Annealed.sigmaBar M n:ℝ) e ω),
        F ω = toHilbertBlockL2OfBlockField hω)
    (hreset :
      let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
      let Q := originCube 2 (n-14)
      let R := upperCellProjectedEnergy M (n+height) Q (Annealed.sigmaBar M n:ℝ)
        (Annealed.sigmaBar M n).property (fun ω => F ω-upperCellResetMeanField Q (F ω))
      Integrable R (Cutoff.cutoffSampleLaw M).toMeasure ∧
        (∫ ω,R ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          upperCellResidualProfile M.gamma (M.gamma*(height:ℝ))) :
    let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
    let Q := originCube 2 (n-14)
    let sigma := (Annealed.sigmaBar M n:ℝ)
    let z := (shellVarianceSum h M.gamma (n+height)-shellVarianceSum h M.gamma n)/(2*sigma^2)
    ∃ C : Cutoff.CutoffSample 2 → Vec 2 → BlockVec 2,
      (∀ ω, ScalarVariation (openCubeSet Q) (C ω)) ∧
      Integrable (cutoffTrialEnergy M (n+height) sigma Q (bandTrialField M n (n+height) sigma e C))
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, cutoffTrialEnergy M (n+height) sigma Q (bandTrialField M n (n+height) sigma e C) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        1+z+upperCellErrorProfile M.gamma (M.gamma*(height:ℝ)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
  let Q := originCube 2 (n-14)
  let sigma := (Annealed.sigmaBar M n:ℝ)
  let z := (shellVarianceSum h M.gamma (n+height)-shellVarianceSum h M.gamma n)/(2*sigma^2)
  let E := upperCellProjectedEnergy M (n+height) Q sigma (Annealed.sigmaBar M n).property
    (fun ω => upperCellResetMeanField Q (F ω))
  let R := upperCellProjectedEnergy M (n+height) Q sigma (Annealed.sigmaBar M n).property
    (fun ω => F ω-upperCellResetMeanField Q (F ω))
  have hp := upper_cell_physical_principal_payment M h hM hg N hpast n hn he F hFm hF
  have ht := upper_cell_projected_energy_triangle M (n+height) Q sigma
    (Annealed.sigmaBar M n).property F hFm hp.1 hreset.1
  have hp' : (∫ ω,E ω ∂μ) ≤ upperCellPrincipalProfile M.gamma z := by
    apply hp.2.trans
    unfold upperCellPrincipalProfile
    exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num)
      M.shellPrefix.gamma_pos.le) (by positivity))
  have hz : z ≤ 9/10 := by
    have hh := upper_cell_potential_variance_gate M h hM n hg (hpast n hn) he
    rw [upper_cell_potential_variance_signal M h hM n height he] at hh
    exact hh.le
  have hr0 : 0 ≤ ∫ ω,R ω ∂μ := integral_nonneg
    (upper_cell_projected_energy_nonneg M (n+height) Q sigma (Annealed.sigmaBar M n).property _)
  have hb := upper_cell_energy_triangle_budget M.gamma (M.gamma*(height:ℝ)) z
    (∫ ω,E ω ∂μ) (∫ ω,R ω ∂μ) hg hz hp' hr0 hreset.2
  obtain ⟨C,hC,hI,hEq⟩ := upper_cell_integrable_trial_from_load
    M n (n+height) sigma (Annealed.sigmaBar M n).property e Q F hFm hF ht.1
  exact ⟨C,hC,hI,hEq.trans_le (ht.2.trans hb)⟩

end
end ASDExplicitGamma.Scalar
