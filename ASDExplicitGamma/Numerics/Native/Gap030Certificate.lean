module
public import ASDExplicitGamma.Numerics.Native.Gap030Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-30 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap030Old_source : nativeOld 30 = nativeGap030Old := by
  unfold nativeOld
  rw [nativeGap030Raw_formula]
  exact nativeGap030Old_formula

theorem nativeGap030Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap030System) *ᵥ nativeVectorReal nativeGap030System.v) i ≤ nativeVectorReal nativeGap030Result i := by
  have hd := nativeGap030Domain
  have hr (i : Fin 21) : nativeGap030System.diag.getD i.val 0+nativeGap030System.subdiag.getD i.val 0+nativeGap030System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap030System.diag.getD i.val 0) (nativeGap030System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap030System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap030Taylor160] at h
  simpa only [nativeGap030Result_formula] using h

end ASDExplicitGamma.Numerics.Native
