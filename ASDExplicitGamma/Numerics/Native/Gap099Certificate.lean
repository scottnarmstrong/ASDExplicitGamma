module
public import ASDExplicitGamma.Numerics.Native.Gap099Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-99 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap099Old_source : nativeOld 99 = nativeGap099Old := by
  unfold nativeOld
  rw [nativeGap099Raw_formula]
  exact nativeGap099Old_formula

theorem nativeGap099Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap099System) *ᵥ nativeVectorReal nativeGap099System.v) i ≤ nativeVectorReal nativeGap099Result i := by
  have hd := nativeGap099Domain
  have hr (i : Fin 21) : nativeGap099System.diag.getD i.val 0+nativeGap099System.subdiag.getD i.val 0+nativeGap099System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap099System.diag.getD i.val 0) (nativeGap099System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap099System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap099Taylor160] at h
  simpa only [nativeGap099Result_formula] using h

end ASDExplicitGamma.Numerics.Native
