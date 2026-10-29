module
public import ASDExplicitGamma.Numerics.Native.Gap153Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-153 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap153Old_source : nativeOld 153 = nativeGap153Old := by
  unfold nativeOld
  rw [nativeGap153Raw_formula]
  exact nativeGap153Old_formula

theorem nativeGap153Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap153System) *ᵥ nativeVectorReal nativeGap153System.v) i ≤ nativeVectorReal nativeGap153Result i := by
  have hd := nativeGap153Domain
  have hr (i : Fin 21) : nativeGap153System.diag.getD i.val 0+nativeGap153System.subdiag.getD i.val 0+nativeGap153System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap153System.diag.getD i.val 0) (nativeGap153System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap153System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap153Taylor160] at h
  simpa only [nativeGap153Result_formula] using h

end ASDExplicitGamma.Numerics.Native
