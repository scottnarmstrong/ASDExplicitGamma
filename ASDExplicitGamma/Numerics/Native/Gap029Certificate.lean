module
public import ASDExplicitGamma.Numerics.Native.Gap029Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-29 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap029Old_source : nativeOld 29 = nativeGap029Old := by
  unfold nativeOld
  rw [nativeGap029Raw_formula]
  exact nativeGap029Old_formula

theorem nativeGap029Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap029System) *ᵥ nativeVectorReal nativeGap029System.v) i ≤ nativeVectorReal nativeGap029Result i := by
  have hd := nativeGap029Domain
  have hr (i : Fin 21) : nativeGap029System.diag.getD i.val 0+nativeGap029System.subdiag.getD i.val 0+nativeGap029System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap029System.diag.getD i.val 0) (nativeGap029System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap029System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap029Taylor160] at h
  simpa only [nativeGap029Result_formula] using h

end ASDExplicitGamma.Numerics.Native
