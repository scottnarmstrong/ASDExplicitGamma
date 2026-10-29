module
public import ASDExplicitGamma.Numerics.Native.Gap025Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-25 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap025Old_source : nativeOld 25 = nativeGap025Old := by
  unfold nativeOld
  rw [nativeGap025Raw_formula]
  exact nativeGap025Old_formula

theorem nativeGap025Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap025System) *ᵥ nativeVectorReal nativeGap025System.v) i ≤ nativeVectorReal nativeGap025Result i := by
  have hd := nativeGap025Domain
  have hr (i : Fin 21) : nativeGap025System.diag.getD i.val 0+nativeGap025System.subdiag.getD i.val 0+nativeGap025System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap025System.diag.getD i.val 0) (nativeGap025System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap025System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap025Taylor160] at h
  simpa only [nativeGap025Result_formula] using h

end ASDExplicitGamma.Numerics.Native
