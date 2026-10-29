module
public import ASDExplicitGamma.Numerics.Native.Gap058Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-58 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap058Old_source : nativeOld 58 = nativeGap058Old := by
  unfold nativeOld
  rw [nativeGap058Raw_formula]
  exact nativeGap058Old_formula

theorem nativeGap058Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap058System) *ᵥ nativeVectorReal nativeGap058System.v) i ≤ nativeVectorReal nativeGap058Result i := by
  have hd := nativeGap058Domain
  have hr (i : Fin 21) : nativeGap058System.diag.getD i.val 0+nativeGap058System.subdiag.getD i.val 0+nativeGap058System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap058System.diag.getD i.val 0) (nativeGap058System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap058System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap058Taylor160] at h
  simpa only [nativeGap058Result_formula] using h

end ASDExplicitGamma.Numerics.Native
