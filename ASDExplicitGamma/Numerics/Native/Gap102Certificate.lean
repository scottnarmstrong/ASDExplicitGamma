module
public import ASDExplicitGamma.Numerics.Native.Gap102Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-102 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap102Old_source : nativeOld 102 = nativeGap102Old := by
  unfold nativeOld
  rw [nativeGap102Raw_formula]
  exact nativeGap102Old_formula

theorem nativeGap102Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap102System) *ᵥ nativeVectorReal nativeGap102System.v) i ≤ nativeVectorReal nativeGap102Result i := by
  have hd := nativeGap102Domain
  have hr (i : Fin 21) : nativeGap102System.diag.getD i.val 0+nativeGap102System.subdiag.getD i.val 0+nativeGap102System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap102System.diag.getD i.val 0) (nativeGap102System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap102System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap102Taylor160] at h
  simpa only [nativeGap102Result_formula] using h

end ASDExplicitGamma.Numerics.Native
