module
public import ASDExplicitGamma.Numerics.Native.Gap038Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-38 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap038Old_source : nativeOld 38 = nativeGap038Old := by
  unfold nativeOld
  rw [nativeGap038Raw_formula]
  exact nativeGap038Old_formula

theorem nativeGap038Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap038System) *ᵥ nativeVectorReal nativeGap038System.v) i ≤ nativeVectorReal nativeGap038Result i := by
  have hd := nativeGap038Domain
  have hr (i : Fin 21) : nativeGap038System.diag.getD i.val 0+nativeGap038System.subdiag.getD i.val 0+nativeGap038System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap038System.diag.getD i.val 0) (nativeGap038System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap038System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap038Taylor160] at h
  simpa only [nativeGap038Result_formula] using h

end ASDExplicitGamma.Numerics.Native
