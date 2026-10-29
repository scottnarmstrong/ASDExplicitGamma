module
public import ASDExplicitGamma.Numerics.Native.Gap110Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-110 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap110Old_source : nativeOld 110 = nativeGap110Old := by
  unfold nativeOld
  rw [nativeGap110Raw_formula]
  exact nativeGap110Old_formula

theorem nativeGap110Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap110System) *ᵥ nativeVectorReal nativeGap110System.v) i ≤ nativeVectorReal nativeGap110Result i := by
  have hd := nativeGap110Domain
  have hr (i : Fin 21) : nativeGap110System.diag.getD i.val 0+nativeGap110System.subdiag.getD i.val 0+nativeGap110System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap110System.diag.getD i.val 0) (nativeGap110System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap110System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap110Taylor160] at h
  simpa only [nativeGap110Result_formula] using h

end ASDExplicitGamma.Numerics.Native
