module
public import ASDExplicitGamma.Numerics.Native.Gap139Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-139 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap139Old_source : nativeOld 139 = nativeGap139Old := by
  unfold nativeOld
  rw [nativeGap139Raw_formula]
  exact nativeGap139Old_formula

theorem nativeGap139Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap139System) *ᵥ nativeVectorReal nativeGap139System.v) i ≤ nativeVectorReal nativeGap139Result i := by
  have hd := nativeGap139Domain
  have hr (i : Fin 21) : nativeGap139System.diag.getD i.val 0+nativeGap139System.subdiag.getD i.val 0+nativeGap139System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap139System.diag.getD i.val 0) (nativeGap139System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap139System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap139Taylor160] at h
  simpa only [nativeGap139Result_formula] using h

end ASDExplicitGamma.Numerics.Native
