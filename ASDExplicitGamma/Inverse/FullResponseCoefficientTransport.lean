module

public import ASDExplicitGamma.Inverse.FullResponseBank
public import ASDExplicitGamma.Inverse.BandCoefficient

/-! Exact completed-base and unit-weight coefficient identities for the bank. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
noncomputable section

/-- Promoting the completed base only sets the intervening weights to one. -/
theorem full_response_coefficient_promote (M : ABKModel 2) (n m N : ℤ)
    (hn : n ≤ m) (hm : m ≤ N) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    attenuatedCoefficient M n N (sourceBandWeights m weights) ω =
      attenuatedCoefficient M m N weights ω := by
  funext x
  rw [attenuated_coefficient_eq_old_add_band M n m N hn hm,
    later_band_skew_embedding]
  rfl

/-- Unit weights recover the full terminal cutoff exactly, sample by sample. -/
theorem full_response_coefficient_unit (M : ABKModel 2) (m N : ℤ)
    (hm : m ≤ N) (ω : Cutoff.CutoffSample 2) :
    attenuatedCoefficient M m N (fun _ => 1) ω = Cutoff.coefficientCutoff M.nu N ω := by
  funext x
  have hc := congrArg (fun a : RegCoeffField 2 => a x) (Cutoff.cutoff_add_finiteShellIncrement ω hm)
  change Cutoff.cutoff m ω x+Cutoff.finiteShellIncrement ω.val m N x=Cutoff.cutoff N ω x at hc
  rw [Cutoff.finiteShellIncrement_apply] at hc
  change Cutoff.cutoff m ω x+(∑ k ∈ Finset.Ioc m N, (ω.val k).forgetShell x)=Cutoff.cutoff N ω x at hc
  simp only [attenuatedCoefficient,Cutoff.coefficientCutoff_apply,one_smul]
  rw [add_assoc,hc]

/-- A one-shell constant attenuation is the literal partially inserted law. -/
theorem full_response_coefficient_partial (M : ABKModel 2) (N : ℤ)
    (s : ℝ) (ω : Cutoff.CutoffSample 2) :
    attenuatedCoefficient M (N-1) N (fun _ => Real.sqrt s) ω =
      fun x => Cutoff.coefficientCutoff M.nu (N-1) ω x+Real.sqrt s • (ω.val N).forgetShell x := by
  funext x
  have hi : Finset.Ioc (N-1) N = {N} := by
    ext k
    simp only [Finset.mem_Ioc,Finset.mem_singleton]
    omega
  simp only [attenuatedCoefficient,hi,Finset.sum_singleton]

end
end ASDExplicitGamma.Inverse
