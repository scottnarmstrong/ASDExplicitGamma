module
public import ASDExplicitGamma.Numerics.Native.Gap075Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-75 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap075Old_source : nativeOld 75 = nativeGap075Old := by
  unfold nativeOld
  rw [nativeGap075Raw_formula]
  exact nativeGap075Old_formula

theorem nativeGap075Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap075System) *ᵥ nativeVectorReal nativeGap075System.v) i ≤ nativeVectorReal nativeGap075Result i := by
  have hd := nativeGap075Domain
  have hr (i : Fin 21) : nativeGap075System.diag.getD i.val 0+nativeGap075System.subdiag.getD i.val 0+nativeGap075System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap075System.diag.getD i.val 0) (nativeGap075System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap075System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap075Taylor160] at h
  simpa only [nativeGap075Result_formula] using h

end ASDExplicitGamma.Numerics.Native
