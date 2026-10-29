module
public import ASDExplicitGamma.Numerics.Native.Gap147Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-147 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap147Old_source : nativeOld 147 = nativeGap147Old := by
  unfold nativeOld
  rw [nativeGap147Raw_formula]
  exact nativeGap147Old_formula

theorem nativeGap147Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap147System) *ᵥ nativeVectorReal nativeGap147System.v) i ≤ nativeVectorReal nativeGap147Result i := by
  have hd := nativeGap147Domain
  have hr (i : Fin 21) : nativeGap147System.diag.getD i.val 0+nativeGap147System.subdiag.getD i.val 0+nativeGap147System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap147System.diag.getD i.val 0) (nativeGap147System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap147System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap147Taylor160] at h
  simpa only [nativeGap147Result_formula] using h

end ASDExplicitGamma.Numerics.Native
