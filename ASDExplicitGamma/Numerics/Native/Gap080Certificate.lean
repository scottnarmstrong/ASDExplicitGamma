module
public import ASDExplicitGamma.Numerics.Native.Gap080Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-80 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap080Old_source : nativeOld 80 = nativeGap080Old := by
  unfold nativeOld
  rw [nativeGap080Raw_formula]
  exact nativeGap080Old_formula

theorem nativeGap080Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap080System) *ᵥ nativeVectorReal nativeGap080System.v) i ≤ nativeVectorReal nativeGap080Result i := by
  have hd := nativeGap080Domain
  have hr (i : Fin 21) : nativeGap080System.diag.getD i.val 0+nativeGap080System.subdiag.getD i.val 0+nativeGap080System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap080System.diag.getD i.val 0) (nativeGap080System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap080System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap080Taylor160] at h
  simpa only [nativeGap080Result_formula] using h

end ASDExplicitGamma.Numerics.Native
