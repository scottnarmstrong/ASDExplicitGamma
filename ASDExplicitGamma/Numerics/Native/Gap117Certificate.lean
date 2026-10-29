module
public import ASDExplicitGamma.Numerics.Native.Gap117Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-117 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap117Old_source : nativeOld 117 = nativeGap117Old := by
  unfold nativeOld
  rw [nativeGap117Raw_formula]
  exact nativeGap117Old_formula

theorem nativeGap117Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap117System) *ᵥ nativeVectorReal nativeGap117System.v) i ≤ nativeVectorReal nativeGap117Result i := by
  have hd := nativeGap117Domain
  have hr (i : Fin 21) : nativeGap117System.diag.getD i.val 0+nativeGap117System.subdiag.getD i.val 0+nativeGap117System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap117System.diag.getD i.val 0) (nativeGap117System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap117System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap117Taylor160] at h
  simpa only [nativeGap117Result_formula] using h

end ASDExplicitGamma.Numerics.Native
