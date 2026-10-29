module
public import ASDExplicitGamma.Numerics.Native.Gap028Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-28 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap028Old_source : nativeOld 28 = nativeGap028Old := by
  unfold nativeOld
  rw [nativeGap028Raw_formula]
  exact nativeGap028Old_formula

theorem nativeGap028Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap028System) *ᵥ nativeVectorReal nativeGap028System.v) i ≤ nativeVectorReal nativeGap028Result i := by
  have hd := nativeGap028Domain
  have hr (i : Fin 21) : nativeGap028System.diag.getD i.val 0+nativeGap028System.subdiag.getD i.val 0+nativeGap028System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap028System.diag.getD i.val 0) (nativeGap028System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap028System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap028Taylor160] at h
  simpa only [nativeGap028Result_formula] using h

end ASDExplicitGamma.Numerics.Native
