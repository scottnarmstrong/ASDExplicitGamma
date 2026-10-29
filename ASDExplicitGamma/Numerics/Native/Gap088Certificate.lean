module
public import ASDExplicitGamma.Numerics.Native.Gap088Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-88 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap088Old_source : nativeOld 88 = nativeGap088Old := by
  unfold nativeOld
  rw [nativeGap088Raw_formula]
  exact nativeGap088Old_formula

theorem nativeGap088Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap088System) *ᵥ nativeVectorReal nativeGap088System.v) i ≤ nativeVectorReal nativeGap088Result i := by
  have hd := nativeGap088Domain
  have hr (i : Fin 21) : nativeGap088System.diag.getD i.val 0+nativeGap088System.subdiag.getD i.val 0+nativeGap088System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap088System.diag.getD i.val 0) (nativeGap088System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap088System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap088Taylor160] at h
  simpa only [nativeGap088Result_formula] using h

end ASDExplicitGamma.Numerics.Native
