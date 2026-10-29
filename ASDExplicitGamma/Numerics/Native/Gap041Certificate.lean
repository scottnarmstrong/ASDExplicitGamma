module
public import ASDExplicitGamma.Numerics.Native.Gap041Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-41 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap041Old_source : nativeOld 41 = nativeGap041Old := by
  unfold nativeOld
  rw [nativeGap041Raw_formula]
  exact nativeGap041Old_formula

theorem nativeGap041Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap041System) *ᵥ nativeVectorReal nativeGap041System.v) i ≤ nativeVectorReal nativeGap041Result i := by
  have hd := nativeGap041Domain
  have hr (i : Fin 21) : nativeGap041System.diag.getD i.val 0+nativeGap041System.subdiag.getD i.val 0+nativeGap041System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap041System.diag.getD i.val 0) (nativeGap041System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap041System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap041Taylor160] at h
  simpa only [nativeGap041Result_formula] using h

end ASDExplicitGamma.Numerics.Native
