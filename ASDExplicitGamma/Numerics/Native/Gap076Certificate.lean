module
public import ASDExplicitGamma.Numerics.Native.Gap076Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-76 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap076Old_source : nativeOld 76 = nativeGap076Old := by
  unfold nativeOld
  rw [nativeGap076Raw_formula]
  exact nativeGap076Old_formula

theorem nativeGap076Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap076System) *ᵥ nativeVectorReal nativeGap076System.v) i ≤ nativeVectorReal nativeGap076Result i := by
  have hd := nativeGap076Domain
  have hr (i : Fin 21) : nativeGap076System.diag.getD i.val 0+nativeGap076System.subdiag.getD i.val 0+nativeGap076System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap076System.diag.getD i.val 0) (nativeGap076System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap076System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap076Taylor160] at h
  simpa only [nativeGap076Result_formula] using h

end ASDExplicitGamma.Numerics.Native
