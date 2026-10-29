module

public import ASDExplicitGamma.Scalar.LawShiftAction

/-! Exact invariance of the full shell law under integer scale shifts. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory ProbabilityTheory
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

/-- Each shifted-and-rescaled shell has exactly its original marginal law. -/
theorem shell_scale_shift_marginal {d : ℕ} (M : ABKModel d) (m k : ℤ) :
    Measure.map (fun ω : ℤ → ShellField d => shellScaleShift M.gamma m ω k) M.P.toMeasure=
      (ShellField.shellMarginalLaw M.P k).toMeasure := by
  change Measure.map (ShellField.triadicScale M.gamma (-m) ∘ (fun ω : ℤ → ShellField d => ω (k+m)))
    M.P.toMeasure=_
  rw [← Measure.map_map (ShellField.measurable_triadicScale M.gamma (-m)) (measurable_pi_apply (k+m))]
  change Measure.map (ShellField.triadicScale M.gamma (-m))
    (ShellField.shellMarginalLaw M.P (k+m)).toMeasure=_
  rw [M.shellPrefix.marginal_scaling (k+m),M.shellPrefix.marginal_scaling k,
    ProbabilityMeasure.toMeasure_map,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (ShellField.measurable_triadicScale M.gamma (-m))
    (ShellField.measurable_triadicScale M.gamma (k+m))]
  congr 1
  funext j
  simp only [Function.comp_apply,shell_triadic_scale_add]
  congr 1
  omega

/-- The whole bi-infinite law, not only its finite moments, is exactly scale-shift invariant. -/
theorem shell_scale_shift_preserves_law {d : ℕ} (M : ABKModel d) (m : ℤ) :
    Measure.map (shellScaleShift M.gamma m) M.P.toMeasure=M.P.toMeasure := by
  have hi := M.shellPrefix.independent.precomp (show Function.Injective (fun k : ℤ => k+m) from
    fun a b h => add_right_cancel h)
  have ht := hi.comp (fun _ => ShellField.triadicScale M.gamma (-m))
    (fun _ => ShellField.measurable_triadicScale M.gamma (-m))
  have hp := ht.map_fun_eq_infinitePi_map (fun k =>
    (ShellField.measurable_triadicScale M.gamma (-m)).comp (measurable_pi_apply (k+m)))
  have hbase := M.shellPrefix.independent.map_fun_eq_infinitePi_map
    (fun k => measurable_pi_apply k)
  change Measure.map (shellScaleShift M.gamma m) M.P.toMeasure=_ at hp
  rw [hp]
  change (Measure.infinitePi (fun k => Measure.map (fun ω : ℤ → ShellField d =>
    ShellField.triadicScale M.gamma (-m) (ω (k+m))) M.P.toMeasure))=M.P.toMeasure
  rw [show (fun k => Measure.map (fun ω : ℤ → ShellField d =>
      ShellField.triadicScale M.gamma (-m) (ω (k+m))) M.P.toMeasure)=
      (fun k => (ShellField.shellMarginalLaw M.P k).toMeasure) by
    funext k
    exact shell_scale_shift_marginal M m k]
  change (Measure.infinitePi (fun k => Measure.map (fun ω : ℤ → ShellField d => ω k) M.P.toMeasure))=M.P.toMeasure
  change Measure.map id M.P.toMeasure=_ at hbase
  rw [Measure.map_id] at hbase
  exact hbase.symm

end ASDExplicitGamma.Scalar
