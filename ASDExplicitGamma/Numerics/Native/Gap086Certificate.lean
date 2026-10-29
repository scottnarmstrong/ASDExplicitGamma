module
public import ASDExplicitGamma.Numerics.Native.Gap086Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-86 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap086Old_source : nativeOld 86 = nativeGap086Old := by
  unfold nativeOld
  rw [nativeGap086Raw_formula]
  exact nativeGap086Old_formula

theorem nativeGap086Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap086System) *ᵥ nativeVectorReal nativeGap086System.v) i ≤ nativeVectorReal nativeGap086Result i := by
  have hd := nativeGap086Domain
  have hr (i : Fin 21) : nativeGap086System.diag.getD i.val 0+nativeGap086System.subdiag.getD i.val 0+nativeGap086System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap086System.diag.getD i.val 0) (nativeGap086System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap086System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap086Taylor160] at h
  simpa only [nativeGap086Result_formula] using h

end ASDExplicitGamma.Numerics.Native
