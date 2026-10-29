module
public import ASDExplicitGamma.Numerics.Native.Gap078Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-78 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap078Old_source : nativeOld 78 = nativeGap078Old := by
  unfold nativeOld
  rw [nativeGap078Raw_formula]
  exact nativeGap078Old_formula

theorem nativeGap078Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap078System) *ᵥ nativeVectorReal nativeGap078System.v) i ≤ nativeVectorReal nativeGap078Result i := by
  have hd := nativeGap078Domain
  have hr (i : Fin 21) : nativeGap078System.diag.getD i.val 0+nativeGap078System.subdiag.getD i.val 0+nativeGap078System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap078System.diag.getD i.val 0) (nativeGap078System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap078System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap078Taylor160] at h
  simpa only [nativeGap078Result_formula] using h

end ASDExplicitGamma.Numerics.Native
