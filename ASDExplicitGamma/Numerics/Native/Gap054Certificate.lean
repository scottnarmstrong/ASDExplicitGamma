module
public import ASDExplicitGamma.Numerics.Native.Gap054Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-54 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap054Old_source : nativeOld 54 = nativeGap054Old := by
  unfold nativeOld
  rw [nativeGap054Raw_formula]
  exact nativeGap054Old_formula

theorem nativeGap054Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap054System) *ᵥ nativeVectorReal nativeGap054System.v) i ≤ nativeVectorReal nativeGap054Result i := by
  have hd := nativeGap054Domain
  have hr (i : Fin 21) : nativeGap054System.diag.getD i.val 0+nativeGap054System.subdiag.getD i.val 0+nativeGap054System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap054System.diag.getD i.val 0) (nativeGap054System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap054System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap054Taylor160] at h
  simpa only [nativeGap054Result_formula] using h

end ASDExplicitGamma.Numerics.Native
