module

public import ASDExplicitGamma.Scalar.UpperCellEnergyTrialBudget
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalErrorCertificate
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetFirstMoment

/-! SC-UPPER-CELL-ENERGY: the actual corrected trial under the standing
outer-target chronology. The physical error is the same profile used in
NU-SC-UPPER-ERROR, with all principal, sensitivity and RESET payments supplied. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Response Algsuperdiff.Section3
noncomputable section

/-- The actual corrected cell trial has expected energy at most 1+z plus
the certified physical error. All energy, moment, independence and source-cap
inputs are proved internally from the standing completed-state chronology. -/
theorem scalar_upper_cell_energy
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (n : ℤ) (hn : n<N)
    {e : Vec 2} (he : Book.Ch02.vecNorm e = 1) :
    let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
    let Q := originCube 2 (n-14)
    let sigma := (Annealed.sigmaBar M n:ℝ)
    let z := (shellVarianceSum h M.gamma (n+height)-shellVarianceSum h M.gamma n)/(2*sigma^2)
    let err := upperCellErrorProfile M.gamma (M.gamma*(height:ℝ))
    err < 681/10000 ∧ ∃ C : Cutoff.CutoffSample 2 → Vec 2 → BlockVec 2,
      (∀ omega, ScalarVariation (openCubeSet Q) (C omega)) ∧
      Integrable (cutoffTrialEnergy M (n+height) sigma Q (bandTrialField M n (n+height) sigma e C))
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ omega, cutoffTrialEnergy M (n+height) sigma Q
        (bandTrialField M n (n+height) sigma e C) omega ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ 1+z+err := by
  refine ⟨(upper_cell_physical_error_certificate M hg).2, ?_⟩
  obtain ⟨F,hFm,hF⟩ := upper_cell_measurable_band_load M n
    (n+⌊(17/50:ℝ)/M.gamma⌋.toNat) (Annealed.sigmaBar M n:ℝ) e (originCube 2 (n-14))
  apply upper_cell_trial_budget_of_reset M h hM hg N hpast n hn he F hFm hF
  have hr := upper_cell_reset_physical_residual_first_moment M h hM hg N hpast n hn e he F hFm
    (by simpa only [Int.floor_toNat] using hF)
  rw [←Int.floor_toNat] at hr
  exact hr

/-- Review interface: the sensitivity scale bounds the literal full-band
compact envelope, and the very error appearing in scalar_upper_cell_energy
is dominated by the exact NU-SC-UPPER-ERROR expression. The fresh envelope is
not a proxy or an assumed bound. -/
theorem scalar_upper_cell_profiles_certified
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k) (n : ℤ) (hn : n<N) :
    let height := ⌊(17/50:ℝ)/M.gamma⌋.toNat
    let Q := originCube 2 (n-14)
    eLpNorm (upperCellPhysicalEnvelope M n height (cubeCenter Q)) 6
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (upperCellFProfile M.gamma) ∧
    upperCellErrorProfile M.gamma (M.gamma*(height:ℝ)) ≤
      Numerics.Mirror.evalReal Numerics.Scalar.scalarRealEnv Numerics.Scalar.upperErrorExpr ∧
    Numerics.Mirror.evalReal Numerics.Scalar.scalarRealEnv Numerics.Scalar.upperErrorExpr < 681/10000 := by
  exact ⟨upper_cell_physical_envelope_eLpNorm_le M h hM n _
    (upper_cell_source_height_pos M hg) _ hg (hpast n hn),
    (upper_cell_physical_error_certificate M hg).1, Numerics.Scalar.upper_error_bounds.1⟩

end
end ASDExplicitGamma.Scalar
