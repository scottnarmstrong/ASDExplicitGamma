module
public import ASDExplicitGamma.Numerics.Native.Gap059Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-59 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap059Old_source : nativeOld 59 = nativeGap059Old := by
  unfold nativeOld
  rw [nativeGap059Raw_formula]
  exact nativeGap059Old_formula

theorem nativeGap059Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap059System) *ᵥ nativeVectorReal nativeGap059System.v) i ≤ nativeVectorReal nativeGap059Result i := by
  have hd := nativeGap059Domain
  have hr (i : Fin 21) : nativeGap059System.diag.getD i.val 0+nativeGap059System.subdiag.getD i.val 0+nativeGap059System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap059System.diag.getD i.val 0) (nativeGap059System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap059System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap059Taylor160] at h
  simpa only [nativeGap059Result_formula] using h

end ASDExplicitGamma.Numerics.Native
