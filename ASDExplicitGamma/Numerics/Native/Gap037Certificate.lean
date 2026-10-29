module
public import ASDExplicitGamma.Numerics.Native.Gap037Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-37 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap037Old_source : nativeOld 37 = nativeGap037Old := by
  unfold nativeOld
  rw [nativeGap037Raw_formula]
  exact nativeGap037Old_formula

theorem nativeGap037Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap037System) *ᵥ nativeVectorReal nativeGap037System.v) i ≤ nativeVectorReal nativeGap037Result i := by
  have hd := nativeGap037Domain
  have hr (i : Fin 21) : nativeGap037System.diag.getD i.val 0+nativeGap037System.subdiag.getD i.val 0+nativeGap037System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap037System.diag.getD i.val 0) (nativeGap037System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap037System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap037Taylor160] at h
  simpa only [nativeGap037Result_formula] using h

end ASDExplicitGamma.Numerics.Native
