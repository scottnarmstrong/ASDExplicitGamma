module

public import ASDExplicitGamma.Main.PartialInsertion
public import ASDExplicitGamma.Model.CellSymmetry

/-! Rotation symmetry of the actual old-frame partial-insertion law. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions

noncomputable section

private theorem main_forgetShell_rotate (R : Mat 2) (hR : IsSignedPermutationMatrix R)
    (j : ShellField 2) :
    ShellField.forgetShell (ShellField.rotate R hR j) =
      rotateReg R hR (ShellField.forgetShell j) := by
  apply RegCoeffField.ext
  intro x
  simp [ShellField.rotate_apply, rotateReg_apply]

private theorem main_forgetShell_rotateAbout (c : Vec 2) (R : Mat 2)
    (hR : IsSignedPermutationMatrix R) (j : ShellField 2) :
    ShellField.forgetShell (Model.rotateShellAbout c R hR j) =
      Model.rotateCoefficientAbout c R hR (ShellField.forgetShell j) := by
  simp only [Model.rotateShellAbout, Model.rotateCoefficientAbout, Function.comp_apply,
    ShellField.forgetShell_translate, main_forgetShell_rotate]

private theorem mainInsertion_combine_rotate (c : Vec 2) (R : Mat 2)
    (hR : IsSignedPermutationMatrix R) (t : ℝ)
    (p : RegCoeffField 2 × ShellField 2) :
    Model.rotateCoefficientAbout c R hR
        (p.1 + Real.sqrt t • ShellField.forgetShell p.2) =
      (Model.rotateCoefficientAbout c R hR p.1) +
        Real.sqrt t • ShellField.forgetShell (Model.rotateShellAbout c R hR p.2) := by
  rw [main_forgetShell_rotateAbout]
  apply RegCoeffField.ext
  intro x
  simp only [Model.rotateCoefficientAbout_apply, RegCoeffField.add_apply,
    RegCoeffField.smul_apply]
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The actual coefficient after a fresh-shell insertion has the same
cell-centered signed-permutation law as the completed OLD coefficient. -/
theorem mainInsertion_coefficient_rotation_law (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (c : Vec 2) (R : Mat 2) (hR : IsSignedPermutationMatrix R) :
    Measure.map
        (fun ω : Cutoff.CutoffSample 2 =>
          Model.rotateCoefficientAbout c R hR (Model.partialInsertedCoefficient M m t ω))
        (Cutoff.cutoffSampleLaw M).toMeasure =
      Measure.map (Model.partialInsertedCoefficient M m t)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μA := (Cutoff.coefficientCutoffLaw M m)
  let μJ := (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let pair : Cutoff.CutoffSample 2 → RegCoeffField 2 × ShellField 2 :=
    fun ω => (Cutoff.coefficientCutoff M.nu m ω, ω.1 (m + 1))
  let combine : RegCoeffField 2 × ShellField 2 → RegCoeffField 2 :=
    fun p => p.1 + Real.sqrt t • ShellField.forgetShell p.2
  let rotatePair : RegCoeffField 2 × ShellField 2 → RegCoeffField 2 × ShellField 2 :=
    fun p => (Model.rotateCoefficientAbout c R hR p.1,
      Model.rotateShellAbout c R hR p.2)
  have hpairMeas : Measurable pair := by
    exact (Cutoff.measurable_coefficientCutoff M.nu m).prodMk
      ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have hpairLaw : Measure.map pair μ = μA.prod μJ := by
    dsimp [pair, μ, μA, μJ]
    calc
      Measure.map (fun ω : Cutoff.CutoffSample 2 =>
          (Cutoff.coefficientCutoff M.nu m ω, ω.1 (m + 1)))
          (Cutoff.cutoffSampleLaw M).toMeasure =
        (Cutoff.coefficientCutoffLaw M m).prod
          (Measure.map (ShellField.triadicScale M.gamma (m + 1))
            (ShellField.zeroShellLaw M.P).toMeasure) := mainInsertion_product_law M m
      _ = (Cutoff.coefficientCutoffLaw M m).prod
          (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure := by
        rw [← Model.map_freshShell_eq_scaledZeroShellLaw,
          Model.map_freshShell_eq_shellMarginalLaw]
  have hcombineMeas : Measurable combine := by
    have hsmul : Measurable (fun a : RegCoeffField 2 => Real.sqrt t • a) := by
      refine measurable_into_regCoeffField' ?_ ?_
      · intro x i j
        exact (measurable_apply_entry x i j).const_smul (Real.sqrt t)
      · intro i j φ hφ
        have hfun : (fun a : RegCoeffField 2 => entryTestR i j φ (Real.sqrt t • a)) =
            fun a => Real.sqrt t * entryTestR i j φ a := by
          funext a
          exact entryTestR_smul i j (Real.sqrt t) a
        rw [hfun]
        exact (measurable_entryTestR i j hφ).const_mul (Real.sqrt t)
    exact measurable_fst.add
      ((hsmul.comp (ShellField.measurable_forgetShell.comp measurable_snd)))
  have hrotAMeas : Measurable (Model.rotateCoefficientAbout c R hR) := by
    exact (measurable_translateReg (-c)).comp
      ((measurable_rotateReg R hR).comp (measurable_translateReg c))
  have hrotJMeas : Measurable (Model.rotateShellAbout c R hR) := by
    exact (ShellField.measurable_translate (-c)).comp
      ((ShellField.measurable_rotate R hR).comp (ShellField.measurable_translate c))
  have hrotPairMeas : Measurable rotatePair :=
    (hrotAMeas.comp measurable_fst).prodMk (hrotJMeas.comp measurable_snd)
  have hA : MeasurePreserving (Model.rotateCoefficientAbout c R hR) μA μA := by
    refine ⟨hrotAMeas, ?_⟩
    exact Model.coefficientCutoffLaw_rotation_about M m c R hR
  have hJ : MeasurePreserving (Model.rotateShellAbout c R hR) μJ μJ := by
    refine ⟨hrotJMeas, ?_⟩
    exact Model.shellMarginalLaw_rotation_about M (m + 1) c R hR
  have hprod : MeasurePreserving rotatePair (μA.prod μJ) (μA.prod μJ) :=
    MeasurePreserving.prod hA hJ
  have hcombineRot : Model.rotateCoefficientAbout c R hR ∘ combine =
      combine ∘ rotatePair := by
    funext p
    exact mainInsertion_combine_rotate c R hR t p
  have hpartial : Model.partialInsertedCoefficient M m t = combine ∘ pair := by
    funext ω
    rw [mainInsertion_coefficient]
    rfl
  calc
    Measure.map
        (fun ω : Cutoff.CutoffSample 2 =>
          Model.rotateCoefficientAbout c R hR (Model.partialInsertedCoefficient M m t ω)) μ
        = Measure.map (Model.rotateCoefficientAbout c R hR ∘ combine) (μA.prod μJ) := by
          change Measure.map ((Model.rotateCoefficientAbout c R hR ∘ combine) ∘ pair) μ = _
          rw [← Measure.map_map (hrotAMeas.comp hcombineMeas) hpairMeas, hpairLaw]
    _ = Measure.map combine (μA.prod μJ) := by
      rw [hcombineRot, ← Measure.map_map hcombineMeas hrotPairMeas, hprod.map_eq]
    _ = Measure.map (Model.partialInsertedCoefficient M m t) μ := by
      rw [← hpairLaw, Measure.map_map hcombineMeas hpairMeas, hpartial]

end

end ASDExplicitGamma.Main
