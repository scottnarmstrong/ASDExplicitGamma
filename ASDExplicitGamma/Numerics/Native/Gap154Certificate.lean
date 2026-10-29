module
public import ASDExplicitGamma.Numerics.Native.Gap154Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-154 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap154Old_source : nativeOld 154 = nativeGap154Old := by
  unfold nativeOld
  rw [nativeGap154Raw_formula]
  exact nativeGap154Old_formula

theorem nativeGap154Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap154System) *ᵥ nativeVectorReal nativeGap154System.v) i ≤ nativeVectorReal nativeGap154Result i := by
  have hd := nativeGap154Domain
  have hr (i : Fin 21) : nativeGap154System.diag.getD i.val 0+nativeGap154System.subdiag.getD i.val 0+nativeGap154System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap154System.diag.getD i.val 0) (nativeGap154System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap154System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap154Taylor160] at h
  simpa only [nativeGap154Result_formula] using h

end ASDExplicitGamma.Numerics.Native
