module
public import ASDExplicitGamma.Numerics.Native.Gap106Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-106 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap106Old_source : nativeOld 106 = nativeGap106Old := by
  unfold nativeOld
  rw [nativeGap106Raw_formula]
  exact nativeGap106Old_formula

theorem nativeGap106Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap106System) *ᵥ nativeVectorReal nativeGap106System.v) i ≤ nativeVectorReal nativeGap106Result i := by
  have hd := nativeGap106Domain
  have hr (i : Fin 21) : nativeGap106System.diag.getD i.val 0+nativeGap106System.subdiag.getD i.val 0+nativeGap106System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap106System.diag.getD i.val 0) (nativeGap106System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap106System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap106Taylor160] at h
  simpa only [nativeGap106Result_formula] using h

end ASDExplicitGamma.Numerics.Native
