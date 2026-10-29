module
public import ASDExplicitGamma.Numerics.Native.Gap061Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-61 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap061Old_source : nativeOld 61 = nativeGap061Old := by
  unfold nativeOld
  rw [nativeGap061Raw_formula]
  exact nativeGap061Old_formula

theorem nativeGap061Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap061System) *ᵥ nativeVectorReal nativeGap061System.v) i ≤ nativeVectorReal nativeGap061Result i := by
  have hd := nativeGap061Domain
  have hr (i : Fin 21) : nativeGap061System.diag.getD i.val 0+nativeGap061System.subdiag.getD i.val 0+nativeGap061System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap061System.diag.getD i.val 0) (nativeGap061System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap061System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap061Taylor160] at h
  simpa only [nativeGap061Result_formula] using h

end ASDExplicitGamma.Numerics.Native
