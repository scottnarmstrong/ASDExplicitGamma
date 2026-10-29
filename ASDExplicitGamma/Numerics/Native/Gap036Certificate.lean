module
public import ASDExplicitGamma.Numerics.Native.Gap036Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-36 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap036Old_source : nativeOld 36 = nativeGap036Old := by
  unfold nativeOld
  rw [nativeGap036Raw_formula]
  exact nativeGap036Old_formula

theorem nativeGap036Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap036System) *ᵥ nativeVectorReal nativeGap036System.v) i ≤ nativeVectorReal nativeGap036Result i := by
  have hd := nativeGap036Domain
  have hr (i : Fin 21) : nativeGap036System.diag.getD i.val 0+nativeGap036System.subdiag.getD i.val 0+nativeGap036System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap036System.diag.getD i.val 0) (nativeGap036System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap036System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap036Taylor160] at h
  simpa only [nativeGap036Result_formula] using h

end ASDExplicitGamma.Numerics.Native
