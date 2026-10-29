module

public import ASDExplicitGamma.Main.ELinearHalfGainPathwise
public import ASDExplicitGamma.Main.HotPatchTrial
public import ASDExplicitGamma.Main.AffineObserverFrame

/-! The `L` group of the hot-patched trial at an arbitrary observer root and
depth, and its samplewise bound by the depth-average of the flat, half-gain
plus-feedback and minus-feedback bills. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff

noncomputable section

local instance eLinearObsPathCubeCompact (Q : TriadicCube 2) :
    CompactSpace (closure (cubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure

/-- The actual partial-insertion response coefficient on an observer root. -/
def mainELinearObsCoefficient (Q : TriadicCube 2) (m : ℤ) (t : ℝ)
    (ω : CutoffSample 2) : ResponseCoefficient (openCubeSet Q) :=
  mainAffineOpenResponseRestriction Q
    (Gaussian.modelInsertedScalar (closure (cubeSet Q)) m t ω)

/-- The `L` group of the hot-patched trial at observer root `Q`, depth `d`,
insertion label `m`: flat energy increment minus its harmonic baseline and
affine-mean part, plus twice the plus and minus affine-source feedback. -/
def mainELinearObsGroup (M : ABKModel 2) (Q : TriadicCube 2) (d : ℕ) (m : ℤ)
    (t b : ℝ) (L : {l : ℝ // 0 < l}) (ω : CutoffSample 2) : ℝ :=
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let k := mainELinearObsCoefficient Q m t ω
  let a := responseFramePlanarCoefficientField M.nu σ k
  let T := hotPatchTrialTerms Q d M.nu σ M.nu_pos hσ k b L
  ∑' j, (T.flat j - oldSignedFlatBoundaryModeEnergy Q b L j -
    oldSignedFlatAffineMode Q d a b L j + 2 * T.feedbackPlus j - 2 * T.feedbackMinus j)

/-- Samplewise bound of the observer-root `L` group. -/
theorem main_e_linear_obs_group_pathwise_bound
    (M : ABKModel 2) (Q : TriadicCube 2) (d : ℕ) (m : ℤ) (t b : ℝ)
    (L : {l : ℝ // 0 < l}) (ω : CutoffSample 2) :
    let σ : ℝ := Annealed.sigmaBar M m
    let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
    let k := mainELinearObsCoefficient Q m t ω
    let a := responseFramePlanarCoefficientField M.nu σ k
    mainELinearObsGroup M Q d m t b L ω ≤
      mainELinearFlatMajorant Q d a b L +
        2 * mainELinearPlusFeedbackHalfGainMajorant Q d M.nu σ M.nu_pos hσ k b L +
        2 * mainELinearMinusFeedbackMajorant Q d M.nu σ M.nu_pos hσ k b L := by
  intro σ hσ k a
  let T := hotPatchTrialTerms Q d M.nu σ M.nu_pos hσ k b L
  have hf := old_signed_flat_signed_energy_bill_directional Q d M.nu σ M.nu_pos hσ k b L
  change Summable T.flat ∧ (∑' n, T.flat n) ≤ _ at hf
  have hp := old_signed_global_plus_feedback_directional_bill_halfgain Q d M.nu σ M.nu_pos hσ k b L
  change Summable T.feedbackPlus ∧ |∑' n, T.feedbackPlus n| ≤ _ at hp
  have hm := old_signed_global_minus_feedback_directional_bill Q d M.nu σ M.nu_pos hσ k b L
  change Summable T.feedbackMinus ∧ |∑' n, T.feedbackMinus n| ≤ _ at hm
  have hB : Summable (oldSignedFlatBoundaryModeEnergy Q b L) :=
    (old_signed_flat_boundary_energy_trace Q b L).summable
  have hA := old_signed_flat_affine_summable Q d a b L
  have hh := (((hf.1.hasSum.sub hB.hasSum).sub hA.hasSum).add
    (hp.1.hasSum.mul_left 2)).sub (hm.1.hasSum.mul_left 2)
  have hEq : mainELinearObsGroup M Q d m t b L ω =
      (∑' n, T.flat n) - oldSignedFlatBoundaryEnergy Q b L -
        oldSignedFlatAffineContribution Q d a b L +
        2 * (∑' n, T.feedbackPlus n) - 2 * (∑' n, T.feedbackMinus n) :=
    hh.tsum_eq
  have hp' := (le_abs_self _).trans hp.2
  have hm' := (neg_le_abs _).trans hm.2
  have hf' := hf.2
  unfold mainELinearFlatMajorant mainELinearPlusFeedbackHalfGainMajorant
    mainELinearMinusFeedbackMajorant
  rw [hEq]
  linarith [hf', hp', hm']

end

end ASDExplicitGamma.Main
