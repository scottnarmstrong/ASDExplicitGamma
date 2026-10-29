module
public import ASDExplicitGamma.Numerics.Native.Gap050Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-50 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap050Old_source : nativeOld 50 = nativeGap050Old := by
  unfold nativeOld
  rw [nativeGap050Raw_formula]
  exact nativeGap050Old_formula

theorem nativeGap050Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap050System) *ᵥ nativeVectorReal nativeGap050System.v) i ≤ nativeVectorReal nativeGap050Result i := by
  have hd := nativeGap050Domain
  have hr (i : Fin 21) : nativeGap050System.diag.getD i.val 0+nativeGap050System.subdiag.getD i.val 0+nativeGap050System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap050System.diag.getD i.val 0) (nativeGap050System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap050System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap050Taylor160] at h
  simpa only [nativeGap050Result_formula] using h

end ASDExplicitGamma.Numerics.Native
