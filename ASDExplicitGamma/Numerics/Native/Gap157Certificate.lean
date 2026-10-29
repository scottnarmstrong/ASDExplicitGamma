module
public import ASDExplicitGamma.Numerics.Native.Gap157Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-157 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap157Old_source : nativeOld 157 = nativeGap157Old := by
  unfold nativeOld
  rw [nativeGap157Raw_formula]
  exact nativeGap157Old_formula

theorem nativeGap157Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap157System) *ᵥ nativeVectorReal nativeGap157System.v) i ≤ nativeVectorReal nativeGap157Result i := by
  have hd := nativeGap157Domain
  have hr (i : Fin 21) : nativeGap157System.diag.getD i.val 0+nativeGap157System.subdiag.getD i.val 0+nativeGap157System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap157System.diag.getD i.val 0) (nativeGap157System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap157System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap157Taylor160] at h
  simpa only [nativeGap157Result_formula] using h

end ASDExplicitGamma.Numerics.Native
