module
public import ASDExplicitGamma.Numerics.Native.Gap150Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-150 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap150Old_source : nativeOld 150 = nativeGap150Old := by
  unfold nativeOld
  rw [nativeGap150Raw_formula]
  exact nativeGap150Old_formula

theorem nativeGap150Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap150System) *ᵥ nativeVectorReal nativeGap150System.v) i ≤ nativeVectorReal nativeGap150Result i := by
  have hd := nativeGap150Domain
  have hr (i : Fin 21) : nativeGap150System.diag.getD i.val 0+nativeGap150System.subdiag.getD i.val 0+nativeGap150System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap150System.diag.getD i.val 0) (nativeGap150System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap150System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap150Taylor160] at h
  simpa only [nativeGap150Result_formula] using h

end ASDExplicitGamma.Numerics.Native
