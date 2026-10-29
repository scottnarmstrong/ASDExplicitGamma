module
public import ASDExplicitGamma.Numerics.Native.Gap159Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-159 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap159Old_source : nativeOld 159 = nativeGap159Old := by
  unfold nativeOld
  rw [nativeGap159Raw_formula]
  exact nativeGap159Old_formula

theorem nativeGap159Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap159System) *ᵥ nativeVectorReal nativeGap159System.v) i ≤ nativeVectorReal nativeGap159Result i := by
  have hd := nativeGap159Domain
  have hr (i : Fin 21) : nativeGap159System.diag.getD i.val 0+nativeGap159System.subdiag.getD i.val 0+nativeGap159System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap159System.diag.getD i.val 0) (nativeGap159System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap159System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap159Taylor160] at h
  simpa only [nativeGap159Result_formula] using h

end ASDExplicitGamma.Numerics.Native
