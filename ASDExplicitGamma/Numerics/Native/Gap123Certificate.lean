module
public import ASDExplicitGamma.Numerics.Native.Gap123Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-123 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap123Old_source : nativeOld 123 = nativeGap123Old := by
  unfold nativeOld
  rw [nativeGap123Raw_formula]
  exact nativeGap123Old_formula

theorem nativeGap123Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap123System) *ᵥ nativeVectorReal nativeGap123System.v) i ≤ nativeVectorReal nativeGap123Result i := by
  have hd := nativeGap123Domain
  have hr (i : Fin 21) : nativeGap123System.diag.getD i.val 0+nativeGap123System.subdiag.getD i.val 0+nativeGap123System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap123System.diag.getD i.val 0) (nativeGap123System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap123System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap123Taylor160] at h
  simpa only [nativeGap123Result_formula] using h

end ASDExplicitGamma.Numerics.Native
