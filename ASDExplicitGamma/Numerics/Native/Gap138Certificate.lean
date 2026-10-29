module
public import ASDExplicitGamma.Numerics.Native.Gap138Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-138 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap138Old_source : nativeOld 138 = nativeGap138Old := by
  unfold nativeOld
  rw [nativeGap138Raw_formula]
  exact nativeGap138Old_formula

theorem nativeGap138Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap138System) *ᵥ nativeVectorReal nativeGap138System.v) i ≤ nativeVectorReal nativeGap138Result i := by
  have hd := nativeGap138Domain
  have hr (i : Fin 21) : nativeGap138System.diag.getD i.val 0+nativeGap138System.subdiag.getD i.val 0+nativeGap138System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap138System.diag.getD i.val 0) (nativeGap138System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap138System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap138Taylor160] at h
  simpa only [nativeGap138Result_formula] using h

end ASDExplicitGamma.Numerics.Native
