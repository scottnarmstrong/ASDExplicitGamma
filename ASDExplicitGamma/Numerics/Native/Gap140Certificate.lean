module
public import ASDExplicitGamma.Numerics.Native.Gap140Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-140 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap140Old_source : nativeOld 140 = nativeGap140Old := by
  unfold nativeOld
  rw [nativeGap140Raw_formula]
  exact nativeGap140Old_formula

theorem nativeGap140Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap140System) *ᵥ nativeVectorReal nativeGap140System.v) i ≤ nativeVectorReal nativeGap140Result i := by
  have hd := nativeGap140Domain
  have hr (i : Fin 21) : nativeGap140System.diag.getD i.val 0+nativeGap140System.subdiag.getD i.val 0+nativeGap140System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap140System.diag.getD i.val 0) (nativeGap140System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap140System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap140Taylor160] at h
  simpa only [nativeGap140Result_formula] using h

end ASDExplicitGamma.Numerics.Native
