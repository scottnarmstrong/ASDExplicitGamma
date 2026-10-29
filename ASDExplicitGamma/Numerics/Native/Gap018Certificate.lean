module
public import ASDExplicitGamma.Numerics.Native.Gap018Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-18 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap018Old_source : nativeOld 18 = nativeGap018Old := by
  unfold nativeOld
  rw [nativeGap018Raw_formula]
  exact nativeGap018Old_formula

theorem nativeGap018Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap018System) *ᵥ nativeVectorReal nativeGap018System.v) i ≤ nativeVectorReal nativeGap018Result i := by
  have hd := nativeGap018Domain
  have hr (i : Fin 21) : nativeGap018System.diag.getD i.val 0+nativeGap018System.subdiag.getD i.val 0+nativeGap018System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap018System.diag.getD i.val 0) (nativeGap018System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap018System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap018Taylor160] at h
  simpa only [nativeGap018Result_formula] using h

end ASDExplicitGamma.Numerics.Native
