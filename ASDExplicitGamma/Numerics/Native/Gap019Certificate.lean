module
public import ASDExplicitGamma.Numerics.Native.Gap019Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-19 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap019Old_source : nativeOld 19 = nativeGap019Old := by
  unfold nativeOld
  rw [nativeGap019Raw_formula]
  exact nativeGap019Old_formula

theorem nativeGap019Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap019System) *ᵥ nativeVectorReal nativeGap019System.v) i ≤ nativeVectorReal nativeGap019Result i := by
  have hd := nativeGap019Domain
  have hr (i : Fin 21) : nativeGap019System.diag.getD i.val 0+nativeGap019System.subdiag.getD i.val 0+nativeGap019System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap019System.diag.getD i.val 0) (nativeGap019System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap019System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap019Taylor160] at h
  simpa only [nativeGap019Result_formula] using h

end ASDExplicitGamma.Numerics.Native
