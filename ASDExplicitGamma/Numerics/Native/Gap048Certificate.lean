module
public import ASDExplicitGamma.Numerics.Native.Gap048Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-48 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap048Old_source : nativeOld 48 = nativeGap048Old := by
  unfold nativeOld
  rw [nativeGap048Raw_formula]
  exact nativeGap048Old_formula

theorem nativeGap048Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap048System) *ᵥ nativeVectorReal nativeGap048System.v) i ≤ nativeVectorReal nativeGap048Result i := by
  have hd := nativeGap048Domain
  have hr (i : Fin 21) : nativeGap048System.diag.getD i.val 0+nativeGap048System.subdiag.getD i.val 0+nativeGap048System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap048System.diag.getD i.val 0) (nativeGap048System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap048System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap048Taylor160] at h
  simpa only [nativeGap048Result_formula] using h

end ASDExplicitGamma.Numerics.Native
