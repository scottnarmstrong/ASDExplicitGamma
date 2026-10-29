module
public import ASDExplicitGamma.Numerics.Native.Gap039Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-39 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap039Old_source : nativeOld 39 = nativeGap039Old := by
  unfold nativeOld
  rw [nativeGap039Raw_formula]
  exact nativeGap039Old_formula

theorem nativeGap039Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap039System) *ᵥ nativeVectorReal nativeGap039System.v) i ≤ nativeVectorReal nativeGap039Result i := by
  have hd := nativeGap039Domain
  have hr (i : Fin 21) : nativeGap039System.diag.getD i.val 0+nativeGap039System.subdiag.getD i.val 0+nativeGap039System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap039System.diag.getD i.val 0) (nativeGap039System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap039System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap039Taylor160] at h
  simpa only [nativeGap039Result_formula] using h

end ASDExplicitGamma.Numerics.Native
