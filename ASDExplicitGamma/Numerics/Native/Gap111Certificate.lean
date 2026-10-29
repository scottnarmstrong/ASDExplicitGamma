module
public import ASDExplicitGamma.Numerics.Native.Gap111Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-111 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap111Old_source : nativeOld 111 = nativeGap111Old := by
  unfold nativeOld
  rw [nativeGap111Raw_formula]
  exact nativeGap111Old_formula

theorem nativeGap111Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap111System) *ᵥ nativeVectorReal nativeGap111System.v) i ≤ nativeVectorReal nativeGap111Result i := by
  have hd := nativeGap111Domain
  have hr (i : Fin 21) : nativeGap111System.diag.getD i.val 0+nativeGap111System.subdiag.getD i.val 0+nativeGap111System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap111System.diag.getD i.val 0) (nativeGap111System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap111System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap111Taylor160] at h
  simpa only [nativeGap111Result_formula] using h

end ASDExplicitGamma.Numerics.Native
