module
public import ASDExplicitGamma.Numerics.Native.Gap081Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-81 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap081Old_source : nativeOld 81 = nativeGap081Old := by
  unfold nativeOld
  rw [nativeGap081Raw_formula]
  exact nativeGap081Old_formula

theorem nativeGap081Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap081System) *ᵥ nativeVectorReal nativeGap081System.v) i ≤ nativeVectorReal nativeGap081Result i := by
  have hd := nativeGap081Domain
  have hr (i : Fin 21) : nativeGap081System.diag.getD i.val 0+nativeGap081System.subdiag.getD i.val 0+nativeGap081System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap081System.diag.getD i.val 0) (nativeGap081System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap081System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap081Taylor160] at h
  simpa only [nativeGap081Result_formula] using h

end ASDExplicitGamma.Numerics.Native
