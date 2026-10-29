module
public import ASDExplicitGamma.Numerics.Native.Gap079Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-79 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap079Old_source : nativeOld 79 = nativeGap079Old := by
  unfold nativeOld
  rw [nativeGap079Raw_formula]
  exact nativeGap079Old_formula

theorem nativeGap079Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap079System) *ᵥ nativeVectorReal nativeGap079System.v) i ≤ nativeVectorReal nativeGap079Result i := by
  have hd := nativeGap079Domain
  have hr (i : Fin 21) : nativeGap079System.diag.getD i.val 0+nativeGap079System.subdiag.getD i.val 0+nativeGap079System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap079System.diag.getD i.val 0) (nativeGap079System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap079System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap079Taylor160] at h
  simpa only [nativeGap079Result_formula] using h

end ASDExplicitGamma.Numerics.Native
