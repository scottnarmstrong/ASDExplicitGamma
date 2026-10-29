module
public import ASDExplicitGamma.Numerics.Native.Gap034Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-34 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap034Old_source : nativeOld 34 = nativeGap034Old := by
  unfold nativeOld
  rw [nativeGap034Raw_formula]
  exact nativeGap034Old_formula

theorem nativeGap034Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap034System) *ᵥ nativeVectorReal nativeGap034System.v) i ≤ nativeVectorReal nativeGap034Result i := by
  have hd := nativeGap034Domain
  have hr (i : Fin 21) : nativeGap034System.diag.getD i.val 0+nativeGap034System.subdiag.getD i.val 0+nativeGap034System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap034System.diag.getD i.val 0) (nativeGap034System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap034System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap034Taylor160] at h
  simpa only [nativeGap034Result_formula] using h

end ASDExplicitGamma.Numerics.Native
