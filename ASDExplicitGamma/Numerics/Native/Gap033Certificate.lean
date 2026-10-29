module
public import ASDExplicitGamma.Numerics.Native.Gap033Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-33 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap033Old_source : nativeOld 33 = nativeGap033Old := by
  unfold nativeOld
  rw [nativeGap033Raw_formula]
  exact nativeGap033Old_formula

theorem nativeGap033Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap033System) *ᵥ nativeVectorReal nativeGap033System.v) i ≤ nativeVectorReal nativeGap033Result i := by
  have hd := nativeGap033Domain
  have hr (i : Fin 21) : nativeGap033System.diag.getD i.val 0+nativeGap033System.subdiag.getD i.val 0+nativeGap033System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap033System.diag.getD i.val 0) (nativeGap033System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap033System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap033Taylor160] at h
  simpa only [nativeGap033Result_formula] using h

end ASDExplicitGamma.Numerics.Native
