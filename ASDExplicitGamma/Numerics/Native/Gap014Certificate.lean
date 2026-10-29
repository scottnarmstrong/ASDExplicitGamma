module
public import ASDExplicitGamma.Numerics.Native.Gap014Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-14 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap014Old_source : nativeOld 14 = nativeGap014Old := by
  unfold nativeOld
  rw [nativeGap014Raw_formula]
  exact nativeGap014Old_formula

theorem nativeGap014Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap014System) *ᵥ nativeVectorReal nativeGap014System.v) i ≤ nativeVectorReal nativeGap014Result i := by
  have hd := nativeGap014Domain
  have hr (i : Fin 21) : nativeGap014System.diag.getD i.val 0+nativeGap014System.subdiag.getD i.val 0+nativeGap014System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap014System.diag.getD i.val 0) (nativeGap014System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap014System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap014Taylor160] at h
  simpa only [nativeGap014Result_formula] using h

end ASDExplicitGamma.Numerics.Native
