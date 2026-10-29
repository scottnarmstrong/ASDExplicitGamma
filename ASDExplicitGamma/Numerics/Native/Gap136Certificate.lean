module
public import ASDExplicitGamma.Numerics.Native.Gap136Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-136 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap136Old_source : nativeOld 136 = nativeGap136Old := by
  unfold nativeOld
  rw [nativeGap136Raw_formula]
  exact nativeGap136Old_formula

theorem nativeGap136Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap136System) *ᵥ nativeVectorReal nativeGap136System.v) i ≤ nativeVectorReal nativeGap136Result i := by
  have hd := nativeGap136Domain
  have hr (i : Fin 21) : nativeGap136System.diag.getD i.val 0+nativeGap136System.subdiag.getD i.val 0+nativeGap136System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap136System.diag.getD i.val 0) (nativeGap136System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap136System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap136Taylor160] at h
  simpa only [nativeGap136Result_formula] using h

end ASDExplicitGamma.Numerics.Native
