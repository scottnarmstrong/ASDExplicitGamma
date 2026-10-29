module
public import ASDExplicitGamma.Numerics.Native.Gap152Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-152 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap152Old_source : nativeOld 152 = nativeGap152Old := by
  unfold nativeOld
  rw [nativeGap152Raw_formula]
  exact nativeGap152Old_formula

theorem nativeGap152Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap152System) *ᵥ nativeVectorReal nativeGap152System.v) i ≤ nativeVectorReal nativeGap152Result i := by
  have hd := nativeGap152Domain
  have hr (i : Fin 21) : nativeGap152System.diag.getD i.val 0+nativeGap152System.subdiag.getD i.val 0+nativeGap152System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap152System.diag.getD i.val 0) (nativeGap152System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap152System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap152Taylor160] at h
  simpa only [nativeGap152Result_formula] using h

end ASDExplicitGamma.Numerics.Native
