module
public import ASDExplicitGamma.Numerics.Native.Gap096Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-96 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap096Old_source : nativeOld 96 = nativeGap096Old := by
  unfold nativeOld
  rw [nativeGap096Raw_formula]
  exact nativeGap096Old_formula

theorem nativeGap096Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap096System) *ᵥ nativeVectorReal nativeGap096System.v) i ≤ nativeVectorReal nativeGap096Result i := by
  have hd := nativeGap096Domain
  have hr (i : Fin 21) : nativeGap096System.diag.getD i.val 0+nativeGap096System.subdiag.getD i.val 0+nativeGap096System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap096System.diag.getD i.val 0) (nativeGap096System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap096System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap096Taylor160] at h
  simpa only [nativeGap096Result_formula] using h

end ASDExplicitGamma.Numerics.Native
