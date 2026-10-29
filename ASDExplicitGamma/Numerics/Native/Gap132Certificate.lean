module
public import ASDExplicitGamma.Numerics.Native.Gap132Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-132 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap132Old_source : nativeOld 132 = nativeGap132Old := by
  unfold nativeOld
  rw [nativeGap132Raw_formula]
  exact nativeGap132Old_formula

theorem nativeGap132Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap132System) *ᵥ nativeVectorReal nativeGap132System.v) i ≤ nativeVectorReal nativeGap132Result i := by
  have hd := nativeGap132Domain
  have hr (i : Fin 21) : nativeGap132System.diag.getD i.val 0+nativeGap132System.subdiag.getD i.val 0+nativeGap132System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap132System.diag.getD i.val 0) (nativeGap132System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap132System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap132Taylor160] at h
  simpa only [nativeGap132Result_formula] using h

end ASDExplicitGamma.Numerics.Native
