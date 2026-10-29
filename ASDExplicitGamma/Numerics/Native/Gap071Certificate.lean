module
public import ASDExplicitGamma.Numerics.Native.Gap071Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-71 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap071Old_source : nativeOld 71 = nativeGap071Old := by
  unfold nativeOld
  rw [nativeGap071Raw_formula]
  exact nativeGap071Old_formula

theorem nativeGap071Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap071System) *ᵥ nativeVectorReal nativeGap071System.v) i ≤ nativeVectorReal nativeGap071Result i := by
  have hd := nativeGap071Domain
  have hr (i : Fin 21) : nativeGap071System.diag.getD i.val 0+nativeGap071System.subdiag.getD i.val 0+nativeGap071System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap071System.diag.getD i.val 0) (nativeGap071System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap071System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap071Taylor160] at h
  simpa only [nativeGap071Result_formula] using h

end ASDExplicitGamma.Numerics.Native
