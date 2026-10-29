module

public import ASDExplicitGamma.Main.EOscillation
public import ASDExplicitGamma.Main.MultiplierMoments
public import ASDExplicitGamma.Statements.GammaZero
public import ASDExplicitGamma.Statements.Theta
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Gaussian.RioTwoSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import ASDExplicitGamma.Main.InverseLowerCenteredBankRow
public import ASDExplicitGamma.Main.InverseDeficitODE
public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Gaussian.ModelHeatResponse
public import ASDExplicitGamma.Scalar.InverseHistory
public import ASDExplicitGamma.Main.EOscillationMinimizer
public import ASDExplicitGamma.Native.OldSignedHistoryCongr
public import ASDExplicitGamma.Native.OldSignedMaxTraceHistory

/-! The exact response-history carrier for the actual partial-insertion law. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- The actual affine source coefficient in the OLD frame is the normalized
physical partial-insertion coefficient used by the multiplier history. -/
theorem main_eosc_response_frame_eq_scaled_partial
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2)
    (ω : CutoffSample 2) (x : Vec 2) (hx : x ∈ openCubeSet Q) :
    responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t Q ω) x =
      (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun x := by
  let k := mainInsertionSkewCoefficient m t Q ω
  let σ : ℝ := Annealed.sigmaBar M m
  have hval : responseCoefficientExtension k x =
      Cutoff.cutoff m ω x 1 0 + Real.sqrt t * (ω.1 (m + 1) x 1 0) := by
    rw [responseCoefficientExtension_eq k hx]
    rfl
  have hcut := Cutoff.cutoff_skew m ω x
  have hcut00 : Cutoff.cutoff m ω x 0 0 = 0 := by
    have hh := congrArg (fun A : Mat 2 => A 0 0) hcut
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hh
    linarith
  have hcut11 : Cutoff.cutoff m ω x 1 1 = 0 := by
    have hh := congrArg (fun A : Mat 2 => A 1 1) hcut
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hh
    linarith
  have hcut01 : Cutoff.cutoff m ω x 0 1 = -Cutoff.cutoff m ω x 1 0 := by
    have hh := congrArg (fun A : Mat 2 => A 0 1) hcut
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at hh
    linarith
  have hcut00' : (∑' r : ℕ, ω.1 (m - (r : ℤ)) x 0 0) = 0 := by
    simpa only [Cutoff.cutoff_apply_entry] using hcut00
  have hcut11' : (∑' r : ℕ, ω.1 (m - (r : ℤ)) x 1 1) = 0 := by
    simpa only [Cutoff.cutoff_apply_entry] using hcut11
  have hcut01' : (∑' r : ℕ, ω.1 (m - (r : ℤ)) x 0 1) =
      -(∑' r : ℕ, ω.1 (m - (r : ℤ)) x 1 0) := by
    simpa only [Cutoff.cutoff_apply_entry] using hcut01
  have hshell := (ω.1 (m + 1)).skew_entry x
  have hshell00 : (ω.1 (m + 1)) x 0 0 = 0 := by
    have hh := hshell 0 0
    linarith
  have hshell11 : (ω.1 (m + 1)) x 1 1 = 0 := by
    have hh := hshell 1 1
    linarith
  have hshell01 : (ω.1 (m + 1)) x 0 1 = -(ω.1 (m + 1)) x 1 0 := by
    have hh := hshell 0 1
    linarith
  have hmodel : (Model.partialInsertedCoefficient M m t ω).toFun x =
      M.nu • (1 : Mat 2) + Cutoff.cutoff m ω x +
        Real.sqrt t • Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell
          (ω.1 (m + 1)) x := by
    rw [mainInsertion_coefficient]
    ext i j
    simp [RegCoeffField.add_apply, RegCoeffField.smul_apply,
      Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply]
  have hσ : σ = Annealed.sigmaBar M m := rfl
  have hσpos : 0 < σ := by
    rw [hσ]
    exact (Annealed.sigmaBar_characterization M m).1
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp only [responseFramePlanarCoefficientField_apply, responsePlanarCoefficient,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, responsePlanarJ]
    rw [hval, hmodel]
    simp only [Cutoff.cutoff_apply_entry]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply]
    simp [hcut00', hcut11', hcut01', hshell00, hshell11, hshell01]
    field_simp [ne_of_gt hσpos] <;> ring

/-- The old full-response history of the source coefficient is exactly the
max-based multiplier history in the same OLD frame. -/
theorem main_eosc_response_history_eq_multiplier_history
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : CutoffSample 2) :
    oldSignedResponseHistory (originCube 2 (m - 5))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)) =
      mainPartialInsertedMultiplierHistory M m t ω := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let σ : ℝ := Annealed.sigmaBar M m
  let a : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ
    (mainInsertionSkewCoefficient m t Q ω)
  let b : CoeffField 2 := (σ : ℝ)⁻¹ •
    (Model.partialInsertedCoefficient M m t ω).toFun
  have hcoef : a =ᵐ[volumeMeasureOn (openCubeSet Q)] b := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact main_eosc_response_frame_eq_scaled_partial M m t Q ω x hx
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1
    (mainInsertionSkewCoefficient m t Q ω)
  have hSeries := old_signed_response_history_series Q a hEll
  rw [hSeries.2]
  change (1 - inverseHistoryDiscount) *
      ∑' j : ℕ, inverseHistoryDiscount ^ j * fullResponseDepthMax Q a j = _
  unfold mainPartialInsertedMultiplierHistory mainPartialInsertedMultiplierDepthMax
  apply congrArg (fun z : ℝ => (1 - inverseHistoryDiscount) * z)
  apply tsum_congr
  intro j
  exact congrArg (fun z : ℝ => inverseHistoryDiscount ^ j * z)
    (old_signed_response_depth_congr Q j a b hcoef)

end
end ASDExplicitGamma.Main
