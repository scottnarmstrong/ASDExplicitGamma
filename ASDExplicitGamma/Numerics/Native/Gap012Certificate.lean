module
public import ASDExplicitGamma.Numerics.Native.Gap012Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-12 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap012Old_source : nativeOld 12 = nativeGap012Old := by
  unfold nativeOld
  rw [nativeGap012Raw_formula]
  exact nativeGap012Old_formula

theorem nativeGap012Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap012System) *ᵥ nativeVectorReal nativeGap012System.v) i ≤ nativeVectorReal nativeGap012Result i := by
  have hd := nativeGap012Domain
  have hr (i : Fin 21) : nativeGap012System.diag.getD i.val 0+nativeGap012System.subdiag.getD i.val 0+nativeGap012System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap012System.diag.getD i.val 0) (nativeGap012System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap012System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap012Taylor160] at h
  simpa only [nativeGap012Result_formula] using h

end ASDExplicitGamma.Numerics.Native
