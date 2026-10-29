module
public import ASDExplicitGamma.Numerics.Native.Gap027Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-27 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap027Old_source : nativeOld 27 = nativeGap027Old := by
  unfold nativeOld
  rw [nativeGap027Raw_formula]
  exact nativeGap027Old_formula

theorem nativeGap027Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap027System) *ᵥ nativeVectorReal nativeGap027System.v) i ≤ nativeVectorReal nativeGap027Result i := by
  have hd := nativeGap027Domain
  have hr (i : Fin 21) : nativeGap027System.diag.getD i.val 0+nativeGap027System.subdiag.getD i.val 0+nativeGap027System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap027System.diag.getD i.val 0) (nativeGap027System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap027System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap027Taylor160] at h
  simpa only [nativeGap027Result_formula] using h

end ASDExplicitGamma.Numerics.Native
