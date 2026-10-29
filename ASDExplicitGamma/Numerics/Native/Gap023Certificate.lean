module
public import ASDExplicitGamma.Numerics.Native.Gap023Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-23 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap023Old_source : nativeOld 23 = nativeGap023Old := by
  unfold nativeOld
  rw [nativeGap023Raw_formula]
  exact nativeGap023Old_formula

theorem nativeGap023Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap023System) *ᵥ nativeVectorReal nativeGap023System.v) i ≤ nativeVectorReal nativeGap023Result i := by
  have hd := nativeGap023Domain
  have hr (i : Fin 21) : nativeGap023System.diag.getD i.val 0+nativeGap023System.subdiag.getD i.val 0+nativeGap023System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap023System.diag.getD i.val 0) (nativeGap023System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap023System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap023Taylor160] at h
  simpa only [nativeGap023Result_formula] using h

end ASDExplicitGamma.Numerics.Native
