module
public import ASDExplicitGamma.Numerics.Native.Gap013Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-13 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap013Old_source : nativeOld 13 = nativeGap013Old := by
  unfold nativeOld
  rw [nativeGap013Raw_formula]
  exact nativeGap013Old_formula

theorem nativeGap013Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap013System) *ᵥ nativeVectorReal nativeGap013System.v) i ≤ nativeVectorReal nativeGap013Result i := by
  have hd := nativeGap013Domain
  have hr (i : Fin 21) : nativeGap013System.diag.getD i.val 0+nativeGap013System.subdiag.getD i.val 0+nativeGap013System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap013System.diag.getD i.val 0) (nativeGap013System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap013System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap013Taylor160] at h
  simpa only [nativeGap013Result_formula] using h

end ASDExplicitGamma.Numerics.Native
