module
public import ASDExplicitGamma.Numerics.Native.Gap129Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-129 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap129Old_source : nativeOld 129 = nativeGap129Old := by
  unfold nativeOld
  rw [nativeGap129Raw_formula]
  exact nativeGap129Old_formula

theorem nativeGap129Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap129System) *ᵥ nativeVectorReal nativeGap129System.v) i ≤ nativeVectorReal nativeGap129Result i := by
  have hd := nativeGap129Domain
  have hr (i : Fin 21) : nativeGap129System.diag.getD i.val 0+nativeGap129System.subdiag.getD i.val 0+nativeGap129System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap129System.diag.getD i.val 0) (nativeGap129System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap129System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap129Taylor160] at h
  simpa only [nativeGap129Result_formula] using h

end ASDExplicitGamma.Numerics.Native
