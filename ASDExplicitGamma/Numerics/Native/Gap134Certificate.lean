module
public import ASDExplicitGamma.Numerics.Native.Gap134Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-134 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap134Old_source : nativeOld 134 = nativeGap134Old := by
  unfold nativeOld
  rw [nativeGap134Raw_formula]
  exact nativeGap134Old_formula

theorem nativeGap134Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap134System) *ᵥ nativeVectorReal nativeGap134System.v) i ≤ nativeVectorReal nativeGap134Result i := by
  have hd := nativeGap134Domain
  have hr (i : Fin 21) : nativeGap134System.diag.getD i.val 0+nativeGap134System.subdiag.getD i.val 0+nativeGap134System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap134System.diag.getD i.val 0) (nativeGap134System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap134System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap134Taylor160] at h
  simpa only [nativeGap134Result_formula] using h

end ASDExplicitGamma.Numerics.Native
