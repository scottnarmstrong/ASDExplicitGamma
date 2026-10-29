module
public import ASDExplicitGamma.Numerics.Native.Gap035Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-35 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap035Old_source : nativeOld 35 = nativeGap035Old := by
  unfold nativeOld
  rw [nativeGap035Raw_formula]
  exact nativeGap035Old_formula

theorem nativeGap035Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap035System) *ᵥ nativeVectorReal nativeGap035System.v) i ≤ nativeVectorReal nativeGap035Result i := by
  have hd := nativeGap035Domain
  have hr (i : Fin 21) : nativeGap035System.diag.getD i.val 0+nativeGap035System.subdiag.getD i.val 0+nativeGap035System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap035System.diag.getD i.val 0) (nativeGap035System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap035System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap035Taylor160] at h
  simpa only [nativeGap035Result_formula] using h

end ASDExplicitGamma.Numerics.Native
