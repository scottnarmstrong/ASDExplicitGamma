module
public import ASDExplicitGamma.Numerics.Native.Gap063Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-63 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap063Old_source : nativeOld 63 = nativeGap063Old := by
  unfold nativeOld
  rw [nativeGap063Raw_formula]
  exact nativeGap063Old_formula

theorem nativeGap063Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap063System) *ᵥ nativeVectorReal nativeGap063System.v) i ≤ nativeVectorReal nativeGap063Result i := by
  have hd := nativeGap063Domain
  have hr (i : Fin 21) : nativeGap063System.diag.getD i.val 0+nativeGap063System.subdiag.getD i.val 0+nativeGap063System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap063System.diag.getD i.val 0) (nativeGap063System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap063System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap063Taylor160] at h
  simpa only [nativeGap063Result_formula] using h

end ASDExplicitGamma.Numerics.Native
