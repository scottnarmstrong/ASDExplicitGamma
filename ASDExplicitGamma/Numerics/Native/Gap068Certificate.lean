module
public import ASDExplicitGamma.Numerics.Native.Gap068Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-68 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap068Old_source : nativeOld 68 = nativeGap068Old := by
  unfold nativeOld
  rw [nativeGap068Raw_formula]
  exact nativeGap068Old_formula

theorem nativeGap068Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap068System) *ᵥ nativeVectorReal nativeGap068System.v) i ≤ nativeVectorReal nativeGap068Result i := by
  have hd := nativeGap068Domain
  have hr (i : Fin 21) : nativeGap068System.diag.getD i.val 0+nativeGap068System.subdiag.getD i.val 0+nativeGap068System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap068System.diag.getD i.val 0) (nativeGap068System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap068System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap068Taylor160] at h
  simpa only [nativeGap068Result_formula] using h

end ASDExplicitGamma.Numerics.Native
