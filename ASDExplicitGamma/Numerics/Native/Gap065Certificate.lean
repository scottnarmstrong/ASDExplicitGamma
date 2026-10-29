module
public import ASDExplicitGamma.Numerics.Native.Gap065Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-65 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap065Old_source : nativeOld 65 = nativeGap065Old := by
  unfold nativeOld
  rw [nativeGap065Raw_formula]
  exact nativeGap065Old_formula

theorem nativeGap065Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap065System) *ᵥ nativeVectorReal nativeGap065System.v) i ≤ nativeVectorReal nativeGap065Result i := by
  have hd := nativeGap065Domain
  have hr (i : Fin 21) : nativeGap065System.diag.getD i.val 0+nativeGap065System.subdiag.getD i.val 0+nativeGap065System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap065System.diag.getD i.val 0) (nativeGap065System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap065System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap065Taylor160] at h
  simpa only [nativeGap065Result_formula] using h

end ASDExplicitGamma.Numerics.Native
