module
public import ASDExplicitGamma.Numerics.Native.Gap098Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-98 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap098Old_source : nativeOld 98 = nativeGap098Old := by
  unfold nativeOld
  rw [nativeGap098Raw_formula]
  exact nativeGap098Old_formula

theorem nativeGap098Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap098System) *ᵥ nativeVectorReal nativeGap098System.v) i ≤ nativeVectorReal nativeGap098Result i := by
  have hd := nativeGap098Domain
  have hr (i : Fin 21) : nativeGap098System.diag.getD i.val 0+nativeGap098System.subdiag.getD i.val 0+nativeGap098System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap098System.diag.getD i.val 0) (nativeGap098System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap098System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap098Taylor160] at h
  simpa only [nativeGap098Result_formula] using h

end ASDExplicitGamma.Numerics.Native
