module
public import ASDExplicitGamma.Numerics.Native.Gap108Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-108 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap108Old_source : nativeOld 108 = nativeGap108Old := by
  unfold nativeOld
  rw [nativeGap108Raw_formula]
  exact nativeGap108Old_formula

theorem nativeGap108Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap108System) *ᵥ nativeVectorReal nativeGap108System.v) i ≤ nativeVectorReal nativeGap108Result i := by
  have hd := nativeGap108Domain
  have hr (i : Fin 21) : nativeGap108System.diag.getD i.val 0+nativeGap108System.subdiag.getD i.val 0+nativeGap108System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap108System.diag.getD i.val 0) (nativeGap108System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap108System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap108Taylor160] at h
  simpa only [nativeGap108Result_formula] using h

end ASDExplicitGamma.Numerics.Native
