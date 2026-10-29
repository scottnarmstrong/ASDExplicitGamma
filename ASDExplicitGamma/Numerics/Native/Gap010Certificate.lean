module
public import ASDExplicitGamma.Numerics.Native.Gap010Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-10 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap010Old_source : nativeOld 10 = nativeGap010Old := by
  unfold nativeOld
  rw [nativeGap010Raw_formula]
  exact nativeGap010Old_formula

theorem nativeGap010Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap010System) *ᵥ nativeVectorReal nativeGap010System.v) i ≤ nativeVectorReal nativeGap010Result i := by
  have hd := nativeGap010Domain
  have hr (i : Fin 21) : nativeGap010System.diag.getD i.val 0+nativeGap010System.subdiag.getD i.val 0+nativeGap010System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap010System.diag.getD i.val 0) (nativeGap010System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap010System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap010Taylor160] at h
  simpa only [nativeGap010Result_formula] using h

end ASDExplicitGamma.Numerics.Native
