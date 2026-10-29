module
public import ASDExplicitGamma.Numerics.Native.Gap021Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-21 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap021Old_source : nativeOld 21 = nativeGap021Old := by
  unfold nativeOld
  rw [nativeGap021Raw_formula]
  exact nativeGap021Old_formula

theorem nativeGap021Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap021System) *ᵥ nativeVectorReal nativeGap021System.v) i ≤ nativeVectorReal nativeGap021Result i := by
  have hd := nativeGap021Domain
  have hr (i : Fin 21) : nativeGap021System.diag.getD i.val 0+nativeGap021System.subdiag.getD i.val 0+nativeGap021System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap021System.diag.getD i.val 0) (nativeGap021System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap021System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap021Taylor160] at h
  simpa only [nativeGap021Result_formula] using h

end ASDExplicitGamma.Numerics.Native
