module
public import ASDExplicitGamma.Numerics.Native.Gap067Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-67 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap067Old_source : nativeOld 67 = nativeGap067Old := by
  unfold nativeOld
  rw [nativeGap067Raw_formula]
  exact nativeGap067Old_formula

theorem nativeGap067Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap067System) *ᵥ nativeVectorReal nativeGap067System.v) i ≤ nativeVectorReal nativeGap067Result i := by
  have hd := nativeGap067Domain
  have hr (i : Fin 21) : nativeGap067System.diag.getD i.val 0+nativeGap067System.subdiag.getD i.val 0+nativeGap067System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap067System.diag.getD i.val 0) (nativeGap067System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap067System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap067Taylor160] at h
  simpa only [nativeGap067Result_formula] using h

end ASDExplicitGamma.Numerics.Native
