module
public import ASDExplicitGamma.Numerics.Native.Gap083Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-83 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap083Old_source : nativeOld 83 = nativeGap083Old := by
  unfold nativeOld
  rw [nativeGap083Raw_formula]
  exact nativeGap083Old_formula

theorem nativeGap083Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap083System) *ᵥ nativeVectorReal nativeGap083System.v) i ≤ nativeVectorReal nativeGap083Result i := by
  have hd := nativeGap083Domain
  have hr (i : Fin 21) : nativeGap083System.diag.getD i.val 0+nativeGap083System.subdiag.getD i.val 0+nativeGap083System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap083System.diag.getD i.val 0) (nativeGap083System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap083System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap083Taylor160] at h
  simpa only [nativeGap083Result_formula] using h

end ASDExplicitGamma.Numerics.Native
