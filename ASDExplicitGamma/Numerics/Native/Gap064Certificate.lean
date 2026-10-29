module
public import ASDExplicitGamma.Numerics.Native.Gap064Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-64 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap064Old_source : nativeOld 64 = nativeGap064Old := by
  unfold nativeOld
  rw [nativeGap064Raw_formula]
  exact nativeGap064Old_formula

theorem nativeGap064Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap064System) *ᵥ nativeVectorReal nativeGap064System.v) i ≤ nativeVectorReal nativeGap064Result i := by
  have hd := nativeGap064Domain
  have hr (i : Fin 21) : nativeGap064System.diag.getD i.val 0+nativeGap064System.subdiag.getD i.val 0+nativeGap064System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap064System.diag.getD i.val 0) (nativeGap064System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap064System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap064Taylor160] at h
  simpa only [nativeGap064Result_formula] using h

end ASDExplicitGamma.Numerics.Native
