module
public import ASDExplicitGamma.Numerics.Native.Gap103Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-103 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap103Old_source : nativeOld 103 = nativeGap103Old := by
  unfold nativeOld
  rw [nativeGap103Raw_formula]
  exact nativeGap103Old_formula

theorem nativeGap103Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap103System) *ᵥ nativeVectorReal nativeGap103System.v) i ≤ nativeVectorReal nativeGap103Result i := by
  have hd := nativeGap103Domain
  have hr (i : Fin 21) : nativeGap103System.diag.getD i.val 0+nativeGap103System.subdiag.getD i.val 0+nativeGap103System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap103System.diag.getD i.val 0) (nativeGap103System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap103System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap103Taylor160] at h
  simpa only [nativeGap103Result_formula] using h

end ASDExplicitGamma.Numerics.Native
