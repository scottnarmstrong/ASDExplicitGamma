module
public import ASDExplicitGamma.Numerics.Native.Gap105Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-105 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap105Old_source : nativeOld 105 = nativeGap105Old := by
  unfold nativeOld
  rw [nativeGap105Raw_formula]
  exact nativeGap105Old_formula

theorem nativeGap105Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap105System) *ᵥ nativeVectorReal nativeGap105System.v) i ≤ nativeVectorReal nativeGap105Result i := by
  have hd := nativeGap105Domain
  have hr (i : Fin 21) : nativeGap105System.diag.getD i.val 0+nativeGap105System.subdiag.getD i.val 0+nativeGap105System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap105System.diag.getD i.val 0) (nativeGap105System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap105System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap105Taylor160] at h
  simpa only [nativeGap105Result_formula] using h

end ASDExplicitGamma.Numerics.Native
