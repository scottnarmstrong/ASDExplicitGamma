module
public import ASDExplicitGamma.Numerics.Native.Gap127Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-127 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap127Old_source : nativeOld 127 = nativeGap127Old := by
  unfold nativeOld
  rw [nativeGap127Raw_formula]
  exact nativeGap127Old_formula

theorem nativeGap127Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap127System) *ᵥ nativeVectorReal nativeGap127System.v) i ≤ nativeVectorReal nativeGap127Result i := by
  have hd := nativeGap127Domain
  have hr (i : Fin 21) : nativeGap127System.diag.getD i.val 0+nativeGap127System.subdiag.getD i.val 0+nativeGap127System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap127System.diag.getD i.val 0) (nativeGap127System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap127System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap127Taylor160] at h
  simpa only [nativeGap127Result_formula] using h

end ASDExplicitGamma.Numerics.Native
