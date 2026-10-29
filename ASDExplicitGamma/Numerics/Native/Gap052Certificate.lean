module
public import ASDExplicitGamma.Numerics.Native.Gap052Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-52 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap052Old_source : nativeOld 52 = nativeGap052Old := by
  unfold nativeOld
  rw [nativeGap052Raw_formula]
  exact nativeGap052Old_formula

theorem nativeGap052Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap052System) *ᵥ nativeVectorReal nativeGap052System.v) i ≤ nativeVectorReal nativeGap052Result i := by
  have hd := nativeGap052Domain
  have hr (i : Fin 21) : nativeGap052System.diag.getD i.val 0+nativeGap052System.subdiag.getD i.val 0+nativeGap052System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap052System.diag.getD i.val 0) (nativeGap052System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap052System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap052Taylor160] at h
  simpa only [nativeGap052Result_formula] using h

end ASDExplicitGamma.Numerics.Native
