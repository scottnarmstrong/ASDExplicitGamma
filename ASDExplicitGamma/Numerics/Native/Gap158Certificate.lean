module
public import ASDExplicitGamma.Numerics.Native.Gap158Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-158 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap158Old_source : nativeOld 158 = nativeGap158Old := by
  unfold nativeOld
  rw [nativeGap158Raw_formula]
  exact nativeGap158Old_formula

theorem nativeGap158Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap158System) *ᵥ nativeVectorReal nativeGap158System.v) i ≤ nativeVectorReal nativeGap158Result i := by
  have hd := nativeGap158Domain
  have hr (i : Fin 21) : nativeGap158System.diag.getD i.val 0+nativeGap158System.subdiag.getD i.val 0+nativeGap158System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap158System.diag.getD i.val 0) (nativeGap158System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap158System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap158Taylor160] at h
  simpa only [nativeGap158Result_formula] using h

end ASDExplicitGamma.Numerics.Native
