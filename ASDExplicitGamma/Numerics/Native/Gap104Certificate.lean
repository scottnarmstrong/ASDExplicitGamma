module
public import ASDExplicitGamma.Numerics.Native.Gap104Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-104 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap104Old_source : nativeOld 104 = nativeGap104Old := by
  unfold nativeOld
  rw [nativeGap104Raw_formula]
  exact nativeGap104Old_formula

theorem nativeGap104Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap104System) *ᵥ nativeVectorReal nativeGap104System.v) i ≤ nativeVectorReal nativeGap104Result i := by
  have hd := nativeGap104Domain
  have hr (i : Fin 21) : nativeGap104System.diag.getD i.val 0+nativeGap104System.subdiag.getD i.val 0+nativeGap104System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap104System.diag.getD i.val 0) (nativeGap104System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap104System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap104Taylor160] at h
  simpa only [nativeGap104Result_formula] using h

end ASDExplicitGamma.Numerics.Native
