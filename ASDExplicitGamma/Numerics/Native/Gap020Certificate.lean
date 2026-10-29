module
public import ASDExplicitGamma.Numerics.Native.Gap020Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-20 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap020Old_source : nativeOld 20 = nativeGap020Old := by
  unfold nativeOld
  rw [nativeGap020Raw_formula]
  exact nativeGap020Old_formula

theorem nativeGap020Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap020System) *ᵥ nativeVectorReal nativeGap020System.v) i ≤ nativeVectorReal nativeGap020Result i := by
  have hd := nativeGap020Domain
  have hr (i : Fin 21) : nativeGap020System.diag.getD i.val 0+nativeGap020System.subdiag.getD i.val 0+nativeGap020System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap020System.diag.getD i.val 0) (nativeGap020System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap020System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap020Taylor160] at h
  simpa only [nativeGap020Result_formula] using h

end ASDExplicitGamma.Numerics.Native
