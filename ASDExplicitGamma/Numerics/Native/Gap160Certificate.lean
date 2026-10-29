module
public import ASDExplicitGamma.Numerics.Native.Gap160Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-160 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap160Old_source : nativeOld 160 = nativeGap160Old := by
  unfold nativeOld
  rw [nativeGap160Raw_formula]
  exact nativeGap160Old_formula

theorem nativeGap160Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap160System) *ᵥ nativeVectorReal nativeGap160System.v) i ≤ nativeVectorReal nativeGap160Result i := by
  have hd := nativeGap160Domain
  have hr (i : Fin 21) : nativeGap160System.diag.getD i.val 0+nativeGap160System.subdiag.getD i.val 0+nativeGap160System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap160System.diag.getD i.val 0) (nativeGap160System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap160System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap160Taylor160] at h
  simpa only [nativeGap160Result_formula] using h

end ASDExplicitGamma.Numerics.Native
