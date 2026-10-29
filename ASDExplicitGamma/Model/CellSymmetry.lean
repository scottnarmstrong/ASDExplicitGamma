module

public import ASDExplicitGamma.Model.CutoffVariance
public import ASDExplicitGamma.Variational.AdapterShearTrace

@[expose] public section

namespace ASDExplicitGamma.Model

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3.Cutoff

noncomputable section

private theorem map_three_eq_self {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g h : X → X) (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfm : Measure.map f μ = μ) (hgm : Measure.map g μ = μ) (hhm : Measure.map h μ = μ) :
    Measure.map (f ∘ g ∘ h) μ = μ := by
  rw [← Measure.map_map hf (hg.comp hh), ← Measure.map_map hg hh, hhm, hgm, hfm]

/-- Shell rotation about a specified centre, in the upstream pullback convention. -/
def rotateShellAbout {d : ℕ} (c : Vec d) (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    ShellField d → ShellField d :=
  ShellField.translate (-c) ∘ ShellField.rotate R hR ∘ ShellField.translate c

/-- Completed coefficient rotation about a specified centre. -/
def rotateCoefficientAbout {d : ℕ} (c : Vec d) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) : RegCoeffField d → RegCoeffField d :=
  translateReg (-c) ∘ rotateReg R hR ∘ translateReg c

/-- The centred action is the literal spatial rotation, with matrix conjugation. -/
theorem rotateCoefficientAbout_apply {d : ℕ} (c : Vec d) (R : Mat d)
    (hR : IsSignedPermutationMatrix R) (a : RegCoeffField d) (x : Vec d) :
    rotateCoefficientAbout c R hR a x =
      matTranspose R * a (matVecMul R (x - c) + c) * R := by
  simp only [rotateCoefficientAbout, Function.comp_apply, translateReg_apply, rotateReg_apply,
    sub_eq_add_neg]

/-- Whole-sequence J3 descends to every actual shell marginal. -/
theorem shellMarginalLaw_rotation {d : ℕ} (M : ABKModel d) (k : ℤ)
    (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measure.map (ShellField.rotate R hR) (ShellField.shellMarginalLaw M.P k).toMeasure =
      (ShellField.shellMarginalLaw M.P k).toMeasure := by
  have hJ3 := congrArg ProbabilityMeasure.toMeasure (M.J3.hyperoctahedral R hR)
  change Measure.map (ShellField.rotateSequence R hR) M.P.toMeasure = M.P.toMeasure at hJ3
  change Measure.map (ShellField.rotate R hR)
    (Measure.map (fun ω : ShellSeq d => ω k) M.P.toMeasure) =
      Measure.map (fun ω : ShellSeq d => ω k) M.P.toMeasure
  rw [Measure.map_map (ShellField.measurable_rotate R hR) (measurable_pi_apply k)]
  change Measure.map ((fun ω : ShellSeq d => ω k) ∘ ShellField.rotateSequence R hR)
    M.P.toMeasure = _
  rw [← Measure.map_map (measurable_pi_apply k) (ShellField.measurable_rotateSequence R hR), hJ3]

/-- Every shell law is invariant under every signed permutation about any
centre, hence under the dihedral group of each planar square cell. -/
theorem shellMarginalLaw_rotation_about {d : ℕ} (M : ABKModel d) (k : ℤ)
    (c : Vec d) (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measure.map (rotateShellAbout c R hR) (ShellField.shellMarginalLaw M.P k).toMeasure =
      (ShellField.shellMarginalLaw M.P k).toMeasure :=
  map_three_eq_self _ _ _ _ (ShellField.measurable_translate (-c))
    (ShellField.measurable_rotate R hR) (ShellField.measurable_translate c)
    (shellMarginalLaw_stationary M k (-c)) (shellMarginalLaw_rotation M k R hR)
    (shellMarginalLaw_stationary M k c)

/-- The completed coefficient law has the same cell-centred dihedral invariance. -/
theorem coefficientCutoffLaw_rotation_about {d : ℕ} (M : ABKModel d) (m : ℤ)
    (c : Vec d) (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measure.map (rotateCoefficientAbout c R hR) (coefficientCutoffLaw M m) =
      coefficientCutoffLaw M m :=
  map_three_eq_self _ _ _ _ (measurable_translateReg (-c))
    (measurable_rotateReg R hR) (measurable_translateReg c)
    (coefficientCutoffLaw_stationary_real M m (-c)) (coefficientCutoffLaw_isotropic M m R hR)
    (coefficientCutoffLaw_stationary_real M m c)

/-- Literal shell-field restriction to a cell retains the centred rotation law. -/
theorem shellMarginalLaw_cellRotation (M : ABKModel 2) (k : ℤ) (Q : TriadicCube 2)
    (R : Mat 2) (hR : IsSignedPermutationMatrix R) :
    Measure.map (fun j : ShellField 2 => fun x : cubeSet Q =>
      rotateShellAbout (cubeCenter Q) R hR j x)
      (ShellField.shellMarginalLaw M.P k).toMeasure =
    Measure.map (fun j : ShellField 2 => fun x : cubeSet Q => j x)
      (ShellField.shellMarginalLaw M.P k).toMeasure := by
  have hr : Measurable (fun j : ShellField 2 => fun x : cubeSet Q => j x) := by
    apply measurable_pi_iff.mpr
    intro x
    change Measurable (fun j : ShellField 2 => j (x : Vec 2))
    exact ShellField.measurable_eval (x : Vec 2)
  have hg := (ShellField.measurable_translate (-(cubeCenter Q))).comp
    ((ShellField.measurable_rotate R hR).comp (ShellField.measurable_translate (cubeCenter Q)))
  change Measure.map ((fun j : ShellField 2 => fun x : cubeSet Q => j x) ∘
    rotateShellAbout (cubeCenter Q) R hR) _ = _
  have hg' : Measurable (rotateShellAbout (cubeCenter Q) R hR) := hg
  rw [← Measure.map_map hr hg', shellMarginalLaw_rotation_about]

/-- Literal completed coefficient restriction to a cell retains the centred
rotation law, rather than merely a finite-dimensional surrogate. -/
theorem coefficientCutoffLaw_cellRotation (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (R : Mat 2) (hR : IsSignedPermutationMatrix R) :
    Measure.map (fun a : RegCoeffField 2 => fun x : cubeSet Q =>
      rotateCoefficientAbout (cubeCenter Q) R hR a x) (coefficientCutoffLaw M m) =
    Measure.map (fun a : RegCoeffField 2 => fun x : cubeSet Q => a x)
      (coefficientCutoffLaw M m) := by
  have hr : Measurable (fun a : RegCoeffField 2 => fun x : cubeSet Q => a x) := by
    apply measurable_pi_iff.mpr
    intro x
    apply measurable_pi_iff.mpr
    intro i
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_apply_entry (x : Vec 2) i j
  have hg := (measurable_translateReg (-(cubeCenter Q))).comp
    ((measurable_rotateReg R hR).comp (measurable_translateReg (cubeCenter Q)))
  change Measure.map ((fun a : RegCoeffField 2 => fun x : cubeSet Q => a x) ∘
    rotateCoefficientAbout (cubeCenter Q) R hR) _ = _
  have hg' : Measurable (rotateCoefficientAbout (cubeCenter Q) R hR) := hg
  rw [← Measure.map_map hr hg', coefficientCutoffLaw_rotation_about]

/-- The planar product covariance is unchanged by a coordinate swap. -/
theorem q3_productCov_swap (x y : ℝ) : q3Cov y * q3Cov x = q3Cov x * q3Cov y := mul_comm _ _

/-- Each coordinate reflection preserves the product covariance. -/
theorem q3_productCov_reflections (x y : ℝ) :
    q3Cov (-x) * q3Cov y = q3Cov x * q3Cov y ∧
      q3Cov x * q3Cov (-y) = q3Cov x * q3Cov y := by
  rw [q3Cov_even, q3Cov_even]
  exact ⟨rfl, rfl⟩

/-- The completed cutoff uses one stationary, mean-zero stream gauge. -/
theorem cutoff_stationary_meanZero (M : ABKModel 2) (m : ℤ) :
    (∀ z : Vec 2, Measure.map (translateReg z) (coefficientCutoffLaw M m) =
      coefficientCutoffLaw M m) ∧
    (∀ x : Vec 2, (∫ ω, cutoffValue m ω x 1 0 ∂(cutoffSampleLaw M).toMeasure) = 0) :=
  ⟨coefficientCutoffLaw_stationary_real M m, cutoff_stream_mean_zero M m⟩

end

end ASDExplicitGamma.Model
