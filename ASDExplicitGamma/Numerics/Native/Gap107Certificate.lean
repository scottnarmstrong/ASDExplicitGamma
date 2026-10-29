module
public import ASDExplicitGamma.Numerics.Native.Gap107Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-107 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap107Old_source : nativeOld 107 = nativeGap107Old := by
  unfold nativeOld
  rw [nativeGap107Raw_formula]
  exact nativeGap107Old_formula

theorem nativeGap107Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap107System) *ᵥ nativeVectorReal nativeGap107System.v) i ≤ nativeVectorReal nativeGap107Result i := by
  have hd := nativeGap107Domain
  have hr (i : Fin 21) : nativeGap107System.diag.getD i.val 0+nativeGap107System.subdiag.getD i.val 0+nativeGap107System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap107System.diag.getD i.val 0) (nativeGap107System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap107System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap107Taylor160] at h
  simpa only [nativeGap107Result_formula] using h

end ASDExplicitGamma.Numerics.Native
