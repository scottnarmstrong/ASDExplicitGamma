module
public import ASDExplicitGamma.Numerics.Native.Gap055Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-55 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap055Old_source : nativeOld 55 = nativeGap055Old := by
  unfold nativeOld
  rw [nativeGap055Raw_formula]
  exact nativeGap055Old_formula

theorem nativeGap055Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap055System) *ᵥ nativeVectorReal nativeGap055System.v) i ≤ nativeVectorReal nativeGap055Result i := by
  have hd := nativeGap055Domain
  have hr (i : Fin 21) : nativeGap055System.diag.getD i.val 0+nativeGap055System.subdiag.getD i.val 0+nativeGap055System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap055System.diag.getD i.val 0) (nativeGap055System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap055System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap055Taylor160] at h
  simpa only [nativeGap055Result_formula] using h

end ASDExplicitGamma.Numerics.Native
