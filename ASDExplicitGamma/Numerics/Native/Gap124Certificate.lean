module
public import ASDExplicitGamma.Numerics.Native.Gap124Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-124 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap124Old_source : nativeOld 124 = nativeGap124Old := by
  unfold nativeOld
  rw [nativeGap124Raw_formula]
  exact nativeGap124Old_formula

theorem nativeGap124Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap124System) *ᵥ nativeVectorReal nativeGap124System.v) i ≤ nativeVectorReal nativeGap124Result i := by
  have hd := nativeGap124Domain
  have hr (i : Fin 21) : nativeGap124System.diag.getD i.val 0+nativeGap124System.subdiag.getD i.val 0+nativeGap124System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap124System.diag.getD i.val 0) (nativeGap124System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap124System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap124Taylor160] at h
  simpa only [nativeGap124Result_formula] using h

end ASDExplicitGamma.Numerics.Native
