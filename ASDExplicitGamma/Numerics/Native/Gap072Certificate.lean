module
public import ASDExplicitGamma.Numerics.Native.Gap072Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-72 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap072Old_source : nativeOld 72 = nativeGap072Old := by
  unfold nativeOld
  rw [nativeGap072Raw_formula]
  exact nativeGap072Old_formula

theorem nativeGap072Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap072System) *ᵥ nativeVectorReal nativeGap072System.v) i ≤ nativeVectorReal nativeGap072Result i := by
  have hd := nativeGap072Domain
  have hr (i : Fin 21) : nativeGap072System.diag.getD i.val 0+nativeGap072System.subdiag.getD i.val 0+nativeGap072System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap072System.diag.getD i.val 0) (nativeGap072System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap072System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap072Taylor160] at h
  simpa only [nativeGap072Result_formula] using h

end ASDExplicitGamma.Numerics.Native
