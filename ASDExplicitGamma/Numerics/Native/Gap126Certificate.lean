module
public import ASDExplicitGamma.Numerics.Native.Gap126Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-126 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap126Old_source : nativeOld 126 = nativeGap126Old := by
  unfold nativeOld
  rw [nativeGap126Raw_formula]
  exact nativeGap126Old_formula

theorem nativeGap126Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap126System) *ᵥ nativeVectorReal nativeGap126System.v) i ≤ nativeVectorReal nativeGap126Result i := by
  have hd := nativeGap126Domain
  have hr (i : Fin 21) : nativeGap126System.diag.getD i.val 0+nativeGap126System.subdiag.getD i.val 0+nativeGap126System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap126System.diag.getD i.val 0) (nativeGap126System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap126System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap126Taylor160] at h
  simpa only [nativeGap126Result_formula] using h

end ASDExplicitGamma.Numerics.Native
