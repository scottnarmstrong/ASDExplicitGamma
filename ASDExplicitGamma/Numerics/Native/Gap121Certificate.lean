module
public import ASDExplicitGamma.Numerics.Native.Gap121Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-121 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap121Old_source : nativeOld 121 = nativeGap121Old := by
  unfold nativeOld
  rw [nativeGap121Raw_formula]
  exact nativeGap121Old_formula

theorem nativeGap121Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap121System) *ᵥ nativeVectorReal nativeGap121System.v) i ≤ nativeVectorReal nativeGap121Result i := by
  have hd := nativeGap121Domain
  have hr (i : Fin 21) : nativeGap121System.diag.getD i.val 0+nativeGap121System.subdiag.getD i.val 0+nativeGap121System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap121System.diag.getD i.val 0) (nativeGap121System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap121System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap121Taylor160] at h
  simpa only [nativeGap121Result_formula] using h

end ASDExplicitGamma.Numerics.Native
