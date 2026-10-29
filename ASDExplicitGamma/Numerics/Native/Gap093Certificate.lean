module
public import ASDExplicitGamma.Numerics.Native.Gap093Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-93 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap093Old_source : nativeOld 93 = nativeGap093Old := by
  unfold nativeOld
  rw [nativeGap093Raw_formula]
  exact nativeGap093Old_formula

theorem nativeGap093Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap093System) *ᵥ nativeVectorReal nativeGap093System.v) i ≤ nativeVectorReal nativeGap093Result i := by
  have hd := nativeGap093Domain
  have hr (i : Fin 21) : nativeGap093System.diag.getD i.val 0+nativeGap093System.subdiag.getD i.val 0+nativeGap093System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap093System.diag.getD i.val 0) (nativeGap093System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap093System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap093Taylor160] at h
  simpa only [nativeGap093Result_formula] using h

end ASDExplicitGamma.Numerics.Native
