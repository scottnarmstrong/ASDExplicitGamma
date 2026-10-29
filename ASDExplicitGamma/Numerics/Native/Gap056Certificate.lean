module
public import ASDExplicitGamma.Numerics.Native.Gap056Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-56 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap056Old_source : nativeOld 56 = nativeGap056Old := by
  unfold nativeOld
  rw [nativeGap056Raw_formula]
  exact nativeGap056Old_formula

theorem nativeGap056Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap056System) *ᵥ nativeVectorReal nativeGap056System.v) i ≤ nativeVectorReal nativeGap056Result i := by
  have hd := nativeGap056Domain
  have hr (i : Fin 21) : nativeGap056System.diag.getD i.val 0+nativeGap056System.subdiag.getD i.val 0+nativeGap056System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap056System.diag.getD i.val 0) (nativeGap056System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap056System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap056Taylor160] at h
  simpa only [nativeGap056Result_formula] using h

end ASDExplicitGamma.Numerics.Native
