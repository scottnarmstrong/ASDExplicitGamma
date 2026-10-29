module
public import ASDExplicitGamma.Numerics.Native.Gap053Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-53 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap053Old_source : nativeOld 53 = nativeGap053Old := by
  unfold nativeOld
  rw [nativeGap053Raw_formula]
  exact nativeGap053Old_formula

theorem nativeGap053Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap053System) *ᵥ nativeVectorReal nativeGap053System.v) i ≤ nativeVectorReal nativeGap053Result i := by
  have hd := nativeGap053Domain
  have hr (i : Fin 21) : nativeGap053System.diag.getD i.val 0+nativeGap053System.subdiag.getD i.val 0+nativeGap053System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap053System.diag.getD i.val 0) (nativeGap053System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap053System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap053Taylor160] at h
  simpa only [nativeGap053Result_formula] using h

end ASDExplicitGamma.Numerics.Native
