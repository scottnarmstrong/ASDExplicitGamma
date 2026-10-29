module
public import ASDExplicitGamma.Numerics.Native.Gap120Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-120 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap120Old_source : nativeOld 120 = nativeGap120Old := by
  unfold nativeOld
  rw [nativeGap120Raw_formula]
  exact nativeGap120Old_formula

theorem nativeGap120Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap120System) *ᵥ nativeVectorReal nativeGap120System.v) i ≤ nativeVectorReal nativeGap120Result i := by
  have hd := nativeGap120Domain
  have hr (i : Fin 21) : nativeGap120System.diag.getD i.val 0+nativeGap120System.subdiag.getD i.val 0+nativeGap120System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap120System.diag.getD i.val 0) (nativeGap120System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap120System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap120Taylor160] at h
  simpa only [nativeGap120Result_formula] using h

end ASDExplicitGamma.Numerics.Native
