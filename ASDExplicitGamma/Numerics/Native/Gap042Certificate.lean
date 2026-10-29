module
public import ASDExplicitGamma.Numerics.Native.Gap042Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-42 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap042Old_source : nativeOld 42 = nativeGap042Old := by
  unfold nativeOld
  rw [nativeGap042Raw_formula]
  exact nativeGap042Old_formula

theorem nativeGap042Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap042System) *ᵥ nativeVectorReal nativeGap042System.v) i ≤ nativeVectorReal nativeGap042Result i := by
  have hd := nativeGap042Domain
  have hr (i : Fin 21) : nativeGap042System.diag.getD i.val 0+nativeGap042System.subdiag.getD i.val 0+nativeGap042System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap042System.diag.getD i.val 0) (nativeGap042System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap042System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap042Taylor160] at h
  simpa only [nativeGap042Result_formula] using h

end ASDExplicitGamma.Numerics.Native
