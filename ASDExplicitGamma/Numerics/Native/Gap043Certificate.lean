module
public import ASDExplicitGamma.Numerics.Native.Gap043Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-43 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap043Old_source : nativeOld 43 = nativeGap043Old := by
  unfold nativeOld
  rw [nativeGap043Raw_formula]
  exact nativeGap043Old_formula

theorem nativeGap043Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap043System) *ᵥ nativeVectorReal nativeGap043System.v) i ≤ nativeVectorReal nativeGap043Result i := by
  have hd := nativeGap043Domain
  have hr (i : Fin 21) : nativeGap043System.diag.getD i.val 0+nativeGap043System.subdiag.getD i.val 0+nativeGap043System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap043System.diag.getD i.val 0) (nativeGap043System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap043System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap043Taylor160] at h
  simpa only [nativeGap043Result_formula] using h

end ASDExplicitGamma.Numerics.Native
