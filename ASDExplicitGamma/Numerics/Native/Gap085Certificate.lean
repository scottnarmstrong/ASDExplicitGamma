module
public import ASDExplicitGamma.Numerics.Native.Gap085Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-85 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap085Old_source : nativeOld 85 = nativeGap085Old := by
  unfold nativeOld
  rw [nativeGap085Raw_formula]
  exact nativeGap085Old_formula

theorem nativeGap085Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap085System) *ᵥ nativeVectorReal nativeGap085System.v) i ≤ nativeVectorReal nativeGap085Result i := by
  have hd := nativeGap085Domain
  have hr (i : Fin 21) : nativeGap085System.diag.getD i.val 0+nativeGap085System.subdiag.getD i.val 0+nativeGap085System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap085System.diag.getD i.val 0) (nativeGap085System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap085System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap085Taylor160] at h
  simpa only [nativeGap085Result_formula] using h

end ASDExplicitGamma.Numerics.Native
