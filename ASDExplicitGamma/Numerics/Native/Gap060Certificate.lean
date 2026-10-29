module
public import ASDExplicitGamma.Numerics.Native.Gap060Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-60 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap060Old_source : nativeOld 60 = nativeGap060Old := by
  unfold nativeOld
  rw [nativeGap060Raw_formula]
  exact nativeGap060Old_formula

theorem nativeGap060Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap060System) *ᵥ nativeVectorReal nativeGap060System.v) i ≤ nativeVectorReal nativeGap060Result i := by
  have hd := nativeGap060Domain
  have hr (i : Fin 21) : nativeGap060System.diag.getD i.val 0+nativeGap060System.subdiag.getD i.val 0+nativeGap060System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap060System.diag.getD i.val 0) (nativeGap060System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap060System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap060Taylor160] at h
  simpa only [nativeGap060Result_formula] using h

end ASDExplicitGamma.Numerics.Native
