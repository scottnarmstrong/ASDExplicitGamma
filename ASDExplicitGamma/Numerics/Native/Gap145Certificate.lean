module
public import ASDExplicitGamma.Numerics.Native.Gap145Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-145 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap145Old_source : nativeOld 145 = nativeGap145Old := by
  unfold nativeOld
  rw [nativeGap145Raw_formula]
  exact nativeGap145Old_formula

theorem nativeGap145Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap145System) *ᵥ nativeVectorReal nativeGap145System.v) i ≤ nativeVectorReal nativeGap145Result i := by
  have hd := nativeGap145Domain
  have hr (i : Fin 21) : nativeGap145System.diag.getD i.val 0+nativeGap145System.subdiag.getD i.val 0+nativeGap145System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap145System.diag.getD i.val 0) (nativeGap145System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap145System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap145Taylor160] at h
  simpa only [nativeGap145Result_formula] using h

end ASDExplicitGamma.Numerics.Native
