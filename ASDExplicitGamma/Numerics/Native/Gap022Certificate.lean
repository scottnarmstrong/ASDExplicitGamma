module
public import ASDExplicitGamma.Numerics.Native.Gap022Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-22 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap022Old_source : nativeOld 22 = nativeGap022Old := by
  unfold nativeOld
  rw [nativeGap022Raw_formula]
  exact nativeGap022Old_formula

theorem nativeGap022Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap022System) *ᵥ nativeVectorReal nativeGap022System.v) i ≤ nativeVectorReal nativeGap022Result i := by
  have hd := nativeGap022Domain
  have hr (i : Fin 21) : nativeGap022System.diag.getD i.val 0+nativeGap022System.subdiag.getD i.val 0+nativeGap022System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap022System.diag.getD i.val 0) (nativeGap022System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap022System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap022Taylor160] at h
  simpa only [nativeGap022Result_formula] using h

end ASDExplicitGamma.Numerics.Native
