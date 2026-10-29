module
public import ASDExplicitGamma.Numerics.Native.Gap149Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-149 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap149Old_source : nativeOld 149 = nativeGap149Old := by
  unfold nativeOld
  rw [nativeGap149Raw_formula]
  exact nativeGap149Old_formula

theorem nativeGap149Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap149System) *ᵥ nativeVectorReal nativeGap149System.v) i ≤ nativeVectorReal nativeGap149Result i := by
  have hd := nativeGap149Domain
  have hr (i : Fin 21) : nativeGap149System.diag.getD i.val 0+nativeGap149System.subdiag.getD i.val 0+nativeGap149System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap149System.diag.getD i.val 0) (nativeGap149System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap149System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap149Taylor160] at h
  simpa only [nativeGap149Result_formula] using h

end ASDExplicitGamma.Numerics.Native
