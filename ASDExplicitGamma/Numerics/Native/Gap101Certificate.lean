module
public import ASDExplicitGamma.Numerics.Native.Gap101Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-101 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap101Old_source : nativeOld 101 = nativeGap101Old := by
  unfold nativeOld
  rw [nativeGap101Raw_formula]
  exact nativeGap101Old_formula

theorem nativeGap101Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap101System) *ᵥ nativeVectorReal nativeGap101System.v) i ≤ nativeVectorReal nativeGap101Result i := by
  have hd := nativeGap101Domain
  have hr (i : Fin 21) : nativeGap101System.diag.getD i.val 0+nativeGap101System.subdiag.getD i.val 0+nativeGap101System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap101System.diag.getD i.val 0) (nativeGap101System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap101System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap101Taylor160] at h
  simpa only [nativeGap101Result_formula] using h

end ASDExplicitGamma.Numerics.Native
