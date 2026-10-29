module
public import ASDExplicitGamma.Numerics.Native.Gap130Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-130 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap130Old_source : nativeOld 130 = nativeGap130Old := by
  unfold nativeOld
  rw [nativeGap130Raw_formula]
  exact nativeGap130Old_formula

theorem nativeGap130Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap130System) *ᵥ nativeVectorReal nativeGap130System.v) i ≤ nativeVectorReal nativeGap130Result i := by
  have hd := nativeGap130Domain
  have hr (i : Fin 21) : nativeGap130System.diag.getD i.val 0+nativeGap130System.subdiag.getD i.val 0+nativeGap130System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap130System.diag.getD i.val 0) (nativeGap130System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap130System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap130Taylor160] at h
  simpa only [nativeGap130Result_formula] using h

end ASDExplicitGamma.Numerics.Native
