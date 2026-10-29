module
public import ASDExplicitGamma.Numerics.Native.Gap062Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-62 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap062Old_source : nativeOld 62 = nativeGap062Old := by
  unfold nativeOld
  rw [nativeGap062Raw_formula]
  exact nativeGap062Old_formula

theorem nativeGap062Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap062System) *ᵥ nativeVectorReal nativeGap062System.v) i ≤ nativeVectorReal nativeGap062Result i := by
  have hd := nativeGap062Domain
  have hr (i : Fin 21) : nativeGap062System.diag.getD i.val 0+nativeGap062System.subdiag.getD i.val 0+nativeGap062System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap062System.diag.getD i.val 0) (nativeGap062System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap062System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap062Taylor160] at h
  simpa only [nativeGap062Result_formula] using h

end ASDExplicitGamma.Numerics.Native
