module
public import ASDExplicitGamma.Numerics.Native.Gap144Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-144 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap144Old_source : nativeOld 144 = nativeGap144Old := by
  unfold nativeOld
  rw [nativeGap144Raw_formula]
  exact nativeGap144Old_formula

theorem nativeGap144Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap144System) *ᵥ nativeVectorReal nativeGap144System.v) i ≤ nativeVectorReal nativeGap144Result i := by
  have hd := nativeGap144Domain
  have hr (i : Fin 21) : nativeGap144System.diag.getD i.val 0+nativeGap144System.subdiag.getD i.val 0+nativeGap144System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap144System.diag.getD i.val 0) (nativeGap144System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap144System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap144Taylor160] at h
  simpa only [nativeGap144Result_formula] using h

end ASDExplicitGamma.Numerics.Native
