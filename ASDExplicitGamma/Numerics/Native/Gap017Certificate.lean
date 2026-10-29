module
public import ASDExplicitGamma.Numerics.Native.Gap017Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-17 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap017Old_source : nativeOld 17 = nativeGap017Old := by
  unfold nativeOld
  rw [nativeGap017Raw_formula]
  exact nativeGap017Old_formula

theorem nativeGap017Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap017System) *ᵥ nativeVectorReal nativeGap017System.v) i ≤ nativeVectorReal nativeGap017Result i := by
  have hd := nativeGap017Domain
  have hr (i : Fin 21) : nativeGap017System.diag.getD i.val 0+nativeGap017System.subdiag.getD i.val 0+nativeGap017System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap017System.diag.getD i.val 0) (nativeGap017System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap017System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap017Taylor160] at h
  simpa only [nativeGap017Result_formula] using h

end ASDExplicitGamma.Numerics.Native
