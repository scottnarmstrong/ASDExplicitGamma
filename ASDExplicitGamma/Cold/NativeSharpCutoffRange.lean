module

public import ASDExplicitGamma.Cold.NativeSharpShellRange
public import Algsuperdiff.Section3.Cutoff.CutoffSampleRange

/-! # Sharp range independence for the genuine infinite cutoff -/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3.Cutoff
namespace ASDExplicitGamma.Cold

/-- Independent literal shell levels give independent sharply separated lower-stream local fields. -/
theorem cold_indep_lowerShellLocalSigma (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (U V : Set (Vec 2)) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsep : ∀ x ∈ U, ∀ y ∈ V, ∃ k : Fin 2, (3:ℝ)^m ≤ |(x-y) k|) :
    Indep (lowerShellLocalSigma m U) (lowerShellLocalSigma m V) M.P.toMeasure := by
  let κ := fun r : ℕ => MeasurableSpace.comap (fun ω : ℤ → ShellField 2 => ω (m-(r:ℤ))) inferInstance
  let a := fun r : ℕ => (ShellField.lihLocalSigma U).comap (fun ω : ℤ → ShellField 2 => ω (m-(r:ℤ)))
  let b := fun r : ℕ => (ShellField.lihLocalSigma V).comap (fun ω : ℤ → ShellField 2 => ω (m-(r:ℤ)))
  have hinj : Function.Injective (fun r : ℕ => m-(r:ℤ)) := by
    intro r s hrs
    exact_mod_cast (sub_right_injective hrs : (r:ℤ) = (s:ℤ))
  have hind : iIndep κ M.P.toMeasure := M.shellPrefix.independent.iIndep.precomp hinj
  have hle : ∀ r, κ r ≤ (inferInstance : MeasurableSpace (ℤ → ShellField 2)) :=
    fun r => (ShellField.measurable_shellCoordinate (m-(r:ℤ))).comap_le
  have ha : ∀ r, a r ≤ κ r := fun _ => MeasurableSpace.comap_mono (ShellField.lihLocalSigma_le_borel U)
  have hb : ∀ r, b r ≤ κ r := fun _ => MeasurableSpace.comap_mono (ShellField.lihLocalSigma_le_borel V)
  have hab : ∀ r, Indep (a r) (b r) M.P.toMeasure := fun r =>
    cold_indep_shellLocal M h hM m (m-(r:ℤ)) (by omega) U V hU hV hsep
  exact Algsuperdiff.Probability.indep_iSup_of_indep_of_iIndep hind hle ha hb hab

/-- Completion and passage to the genuine cutoff subtype retain the sharp coordinate range. -/
theorem cold_indep_cutoffSampleLocalSigma (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (U V : Set (Vec 2)) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hsep : ∀ x ∈ U, ∀ y ∈ V, ∃ k : Fin 2, (3:ℝ)^m ≤ |(x-y) k|) :
    Indep (cutoffSampleLocalSigma M m U) (cutoffSampleLocalSigma M m V) (cutoffSampleLaw M).toMeasure := by
  apply indep_cutoffSampleLocalSigma_of_indep_completion
  apply indep_lowerShellLocalCompletion_of_indep
  exact cold_indep_lowerShellLocalSigma M h hM m U V hU hV hsep

end ASDExplicitGamma.Cold
