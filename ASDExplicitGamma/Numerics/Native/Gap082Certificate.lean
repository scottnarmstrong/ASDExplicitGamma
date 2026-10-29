module
public import ASDExplicitGamma.Numerics.Native.Gap082Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-82 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap082Old_source : nativeOld 82 = nativeGap082Old := by
  unfold nativeOld
  rw [nativeGap082Raw_formula]
  exact nativeGap082Old_formula

theorem nativeGap082Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap082System) *ᵥ nativeVectorReal nativeGap082System.v) i ≤ nativeVectorReal nativeGap082Result i := by
  have hd := nativeGap082Domain
  have hr (i : Fin 21) : nativeGap082System.diag.getD i.val 0+nativeGap082System.subdiag.getD i.val 0+nativeGap082System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap082System.diag.getD i.val 0) (nativeGap082System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap082System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap082Taylor160] at h
  simpa only [nativeGap082Result_formula] using h

end ASDExplicitGamma.Numerics.Native
