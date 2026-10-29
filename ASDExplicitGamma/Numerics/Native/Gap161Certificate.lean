module
public import ASDExplicitGamma.Numerics.Native.Gap161Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-161 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap161Old_source : nativeOld 161 = nativeGap161Old := by
  unfold nativeOld
  rw [nativeGap161Raw_formula]
  exact nativeGap161Old_formula

theorem nativeGap161Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap161System) *ᵥ nativeVectorReal nativeGap161System.v) i ≤ nativeVectorReal nativeGap161Result i := by
  have hd := nativeGap161Domain
  have hr (i : Fin 21) : nativeGap161System.diag.getD i.val 0+nativeGap161System.subdiag.getD i.val 0+nativeGap161System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap161System.diag.getD i.val 0) (nativeGap161System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap161System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap161Taylor160] at h
  simpa only [nativeGap161Result_formula] using h

end ASDExplicitGamma.Numerics.Native
