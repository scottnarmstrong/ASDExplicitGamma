module
public import ASDExplicitGamma.Numerics.Native.Gap128Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-128 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap128Old_source : nativeOld 128 = nativeGap128Old := by
  unfold nativeOld
  rw [nativeGap128Raw_formula]
  exact nativeGap128Old_formula

theorem nativeGap128Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap128System) *ᵥ nativeVectorReal nativeGap128System.v) i ≤ nativeVectorReal nativeGap128Result i := by
  have hd := nativeGap128Domain
  have hr (i : Fin 21) : nativeGap128System.diag.getD i.val 0+nativeGap128System.subdiag.getD i.val 0+nativeGap128System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap128System.diag.getD i.val 0) (nativeGap128System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap128System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap128Taylor160] at h
  simpa only [nativeGap128Result_formula] using h

end ASDExplicitGamma.Numerics.Native
