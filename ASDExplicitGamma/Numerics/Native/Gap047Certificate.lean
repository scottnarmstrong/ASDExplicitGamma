module
public import ASDExplicitGamma.Numerics.Native.Gap047Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-47 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap047Old_source : nativeOld 47 = nativeGap047Old := by
  unfold nativeOld
  rw [nativeGap047Raw_formula]
  exact nativeGap047Old_formula

theorem nativeGap047Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap047System) *ᵥ nativeVectorReal nativeGap047System.v) i ≤ nativeVectorReal nativeGap047Result i := by
  have hd := nativeGap047Domain
  have hr (i : Fin 21) : nativeGap047System.diag.getD i.val 0+nativeGap047System.subdiag.getD i.val 0+nativeGap047System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap047System.diag.getD i.val 0) (nativeGap047System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap047System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap047Taylor160] at h
  simpa only [nativeGap047Result_formula] using h

end ASDExplicitGamma.Numerics.Native
