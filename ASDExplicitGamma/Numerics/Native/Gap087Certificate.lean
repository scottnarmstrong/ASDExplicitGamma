module
public import ASDExplicitGamma.Numerics.Native.Gap087Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-87 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap087Old_source : nativeOld 87 = nativeGap087Old := by
  unfold nativeOld
  rw [nativeGap087Raw_formula]
  exact nativeGap087Old_formula

theorem nativeGap087Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap087System) *ᵥ nativeVectorReal nativeGap087System.v) i ≤ nativeVectorReal nativeGap087Result i := by
  have hd := nativeGap087Domain
  have hr (i : Fin 21) : nativeGap087System.diag.getD i.val 0+nativeGap087System.subdiag.getD i.val 0+nativeGap087System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap087System.diag.getD i.val 0) (nativeGap087System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap087System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap087Taylor160] at h
  simpa only [nativeGap087Result_formula] using h

end ASDExplicitGamma.Numerics.Native
