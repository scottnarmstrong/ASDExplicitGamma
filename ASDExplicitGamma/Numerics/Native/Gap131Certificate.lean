module
public import ASDExplicitGamma.Numerics.Native.Gap131Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-131 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap131Old_source : nativeOld 131 = nativeGap131Old := by
  unfold nativeOld
  rw [nativeGap131Raw_formula]
  exact nativeGap131Old_formula

theorem nativeGap131Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap131System) *ᵥ nativeVectorReal nativeGap131System.v) i ≤ nativeVectorReal nativeGap131Result i := by
  have hd := nativeGap131Domain
  have hr (i : Fin 21) : nativeGap131System.diag.getD i.val 0+nativeGap131System.subdiag.getD i.val 0+nativeGap131System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap131System.diag.getD i.val 0) (nativeGap131System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap131System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap131Taylor160] at h
  simpa only [nativeGap131Result_formula] using h

end ASDExplicitGamma.Numerics.Native
