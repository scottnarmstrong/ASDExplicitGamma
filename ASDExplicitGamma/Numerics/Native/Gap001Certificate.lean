module
public import ASDExplicitGamma.Numerics.Native.Gap001Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-1 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap001Old_source : nativeOld 1 = nativeGap001Old := by
  unfold nativeOld
  rw [nativeGap001Raw_formula]
  exact nativeGap001Old_formula

theorem nativeGap001Scale_pos : 0 < nativeGap001Scale := by
  decide +kernel

theorem nativeGap001Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap001System) *ᵥ nativeVectorReal nativeGap001System.v) i ≤ nativeVectorReal nativeGap001Result i := by
  have hd := nativeGap001Domain
  have hr (i : Fin 21) : nativeGap001System.diag.getD i.val 0+nativeGap001System.subdiag.getD i.val 0+nativeGap001System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap001System.diag.getD i.val 0) (nativeGap001System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap001System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap001Taylor160] at h
  simpa only [nativeGap001Result_formula] using h

end ASDExplicitGamma.Numerics.Native
