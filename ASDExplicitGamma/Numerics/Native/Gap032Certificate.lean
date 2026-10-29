module
public import ASDExplicitGamma.Numerics.Native.Gap032Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-32 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap032Old_source : nativeOld 32 = nativeGap032Old := by
  unfold nativeOld
  rw [nativeGap032Raw_formula]
  exact nativeGap032Old_formula

theorem nativeGap032Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap032System) *ᵥ nativeVectorReal nativeGap032System.v) i ≤ nativeVectorReal nativeGap032Result i := by
  have hd := nativeGap032Domain
  have hr (i : Fin 21) : nativeGap032System.diag.getD i.val 0+nativeGap032System.subdiag.getD i.val 0+nativeGap032System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap032System.diag.getD i.val 0) (nativeGap032System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap032System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap032Taylor160] at h
  simpa only [nativeGap032Result_formula] using h

end ASDExplicitGamma.Numerics.Native
