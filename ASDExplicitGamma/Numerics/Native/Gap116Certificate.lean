module
public import ASDExplicitGamma.Numerics.Native.Gap116Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-116 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap116Old_source : nativeOld 116 = nativeGap116Old := by
  unfold nativeOld
  rw [nativeGap116Raw_formula]
  exact nativeGap116Old_formula

theorem nativeGap116Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap116System) *ᵥ nativeVectorReal nativeGap116System.v) i ≤ nativeVectorReal nativeGap116Result i := by
  have hd := nativeGap116Domain
  have hr (i : Fin 21) : nativeGap116System.diag.getD i.val 0+nativeGap116System.subdiag.getD i.val 0+nativeGap116System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap116System.diag.getD i.val 0) (nativeGap116System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap116System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap116Taylor160] at h
  simpa only [nativeGap116Result_formula] using h

end ASDExplicitGamma.Numerics.Native
