module
public import ASDExplicitGamma.Numerics.Native.Gap151Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-151 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap151Old_source : nativeOld 151 = nativeGap151Old := by
  unfold nativeOld
  rw [nativeGap151Raw_formula]
  exact nativeGap151Old_formula

theorem nativeGap151Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap151System) *ᵥ nativeVectorReal nativeGap151System.v) i ≤ nativeVectorReal nativeGap151Result i := by
  have hd := nativeGap151Domain
  have hr (i : Fin 21) : nativeGap151System.diag.getD i.val 0+nativeGap151System.subdiag.getD i.val 0+nativeGap151System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap151System.diag.getD i.val 0) (nativeGap151System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap151System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap151Taylor160] at h
  simpa only [nativeGap151Result_formula] using h

end ASDExplicitGamma.Numerics.Native
