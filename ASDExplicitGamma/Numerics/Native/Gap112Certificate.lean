module
public import ASDExplicitGamma.Numerics.Native.Gap112Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-112 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap112Old_source : nativeOld 112 = nativeGap112Old := by
  unfold nativeOld
  rw [nativeGap112Raw_formula]
  exact nativeGap112Old_formula

theorem nativeGap112Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap112System) *ᵥ nativeVectorReal nativeGap112System.v) i ≤ nativeVectorReal nativeGap112Result i := by
  have hd := nativeGap112Domain
  have hr (i : Fin 21) : nativeGap112System.diag.getD i.val 0+nativeGap112System.subdiag.getD i.val 0+nativeGap112System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap112System.diag.getD i.val 0) (nativeGap112System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap112System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap112Taylor160] at h
  simpa only [nativeGap112Result_formula] using h

end ASDExplicitGamma.Numerics.Native
