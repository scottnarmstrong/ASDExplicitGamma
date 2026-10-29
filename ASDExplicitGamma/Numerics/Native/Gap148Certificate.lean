module
public import ASDExplicitGamma.Numerics.Native.Gap148Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-148 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap148Old_source : nativeOld 148 = nativeGap148Old := by
  unfold nativeOld
  rw [nativeGap148Raw_formula]
  exact nativeGap148Old_formula

theorem nativeGap148Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap148System) *ᵥ nativeVectorReal nativeGap148System.v) i ≤ nativeVectorReal nativeGap148Result i := by
  have hd := nativeGap148Domain
  have hr (i : Fin 21) : nativeGap148System.diag.getD i.val 0+nativeGap148System.subdiag.getD i.val 0+nativeGap148System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap148System.diag.getD i.val 0) (nativeGap148System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap148System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap148Taylor160] at h
  simpa only [nativeGap148Result_formula] using h

end ASDExplicitGamma.Numerics.Native
