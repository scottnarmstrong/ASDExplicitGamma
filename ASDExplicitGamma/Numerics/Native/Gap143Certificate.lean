module
public import ASDExplicitGamma.Numerics.Native.Gap143Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-143 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap143Old_source : nativeOld 143 = nativeGap143Old := by
  unfold nativeOld
  rw [nativeGap143Raw_formula]
  exact nativeGap143Old_formula

theorem nativeGap143Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap143System) *ᵥ nativeVectorReal nativeGap143System.v) i ≤ nativeVectorReal nativeGap143Result i := by
  have hd := nativeGap143Domain
  have hr (i : Fin 21) : nativeGap143System.diag.getD i.val 0+nativeGap143System.subdiag.getD i.val 0+nativeGap143System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap143System.diag.getD i.val 0) (nativeGap143System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap143System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap143Taylor160] at h
  simpa only [nativeGap143Result_formula] using h

end ASDExplicitGamma.Numerics.Native
