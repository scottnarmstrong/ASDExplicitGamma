module
public import ASDExplicitGamma.Numerics.Native.Gap142Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-142 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap142Old_source : nativeOld 142 = nativeGap142Old := by
  unfold nativeOld
  rw [nativeGap142Raw_formula]
  exact nativeGap142Old_formula

theorem nativeGap142Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap142System) *ᵥ nativeVectorReal nativeGap142System.v) i ≤ nativeVectorReal nativeGap142Result i := by
  have hd := nativeGap142Domain
  have hr (i : Fin 21) : nativeGap142System.diag.getD i.val 0+nativeGap142System.subdiag.getD i.val 0+nativeGap142System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap142System.diag.getD i.val 0) (nativeGap142System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap142System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap142Taylor160] at h
  simpa only [nativeGap142Result_formula] using h

end ASDExplicitGamma.Numerics.Native
