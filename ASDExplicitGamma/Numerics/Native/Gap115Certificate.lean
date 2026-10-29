module
public import ASDExplicitGamma.Numerics.Native.Gap115Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-115 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap115Old_source : nativeOld 115 = nativeGap115Old := by
  unfold nativeOld
  rw [nativeGap115Raw_formula]
  exact nativeGap115Old_formula

theorem nativeGap115Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap115System) *ᵥ nativeVectorReal nativeGap115System.v) i ≤ nativeVectorReal nativeGap115Result i := by
  have hd := nativeGap115Domain
  have hr (i : Fin 21) : nativeGap115System.diag.getD i.val 0+nativeGap115System.subdiag.getD i.val 0+nativeGap115System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap115System.diag.getD i.val 0) (nativeGap115System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap115System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap115Taylor160] at h
  simpa only [nativeGap115Result_formula] using h

end ASDExplicitGamma.Numerics.Native
