module
public import ASDExplicitGamma.Numerics.Native.Gap049Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-49 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap049Old_source : nativeOld 49 = nativeGap049Old := by
  unfold nativeOld
  rw [nativeGap049Raw_formula]
  exact nativeGap049Old_formula

theorem nativeGap049Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap049System) *ᵥ nativeVectorReal nativeGap049System.v) i ≤ nativeVectorReal nativeGap049Result i := by
  have hd := nativeGap049Domain
  have hr (i : Fin 21) : nativeGap049System.diag.getD i.val 0+nativeGap049System.subdiag.getD i.val 0+nativeGap049System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap049System.diag.getD i.val 0) (nativeGap049System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap049System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap049Taylor160] at h
  simpa only [nativeGap049Result_formula] using h

end ASDExplicitGamma.Numerics.Native
