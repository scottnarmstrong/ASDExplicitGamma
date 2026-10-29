module
public import ASDExplicitGamma.Numerics.Native.Gap051Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-51 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap051Old_source : nativeOld 51 = nativeGap051Old := by
  unfold nativeOld
  rw [nativeGap051Raw_formula]
  exact nativeGap051Old_formula

theorem nativeGap051Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap051System) *ᵥ nativeVectorReal nativeGap051System.v) i ≤ nativeVectorReal nativeGap051Result i := by
  have hd := nativeGap051Domain
  have hr (i : Fin 21) : nativeGap051System.diag.getD i.val 0+nativeGap051System.subdiag.getD i.val 0+nativeGap051System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap051System.diag.getD i.val 0) (nativeGap051System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap051System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap051Taylor160] at h
  simpa only [nativeGap051Result_formula] using h

end ASDExplicitGamma.Numerics.Native
