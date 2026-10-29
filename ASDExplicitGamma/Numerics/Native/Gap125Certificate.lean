module
public import ASDExplicitGamma.Numerics.Native.Gap125Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-125 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap125Old_source : nativeOld 125 = nativeGap125Old := by
  unfold nativeOld
  rw [nativeGap125Raw_formula]
  exact nativeGap125Old_formula

theorem nativeGap125Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap125System) *ᵥ nativeVectorReal nativeGap125System.v) i ≤ nativeVectorReal nativeGap125Result i := by
  have hd := nativeGap125Domain
  have hr (i : Fin 21) : nativeGap125System.diag.getD i.val 0+nativeGap125System.subdiag.getD i.val 0+nativeGap125System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap125System.diag.getD i.val 0) (nativeGap125System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap125System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap125Taylor160] at h
  simpa only [nativeGap125Result_formula] using h

end ASDExplicitGamma.Numerics.Native
