module
public import ASDExplicitGamma.Numerics.Native.Gap074Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-74 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap074Old_source : nativeOld 74 = nativeGap074Old := by
  unfold nativeOld
  rw [nativeGap074Raw_formula]
  exact nativeGap074Old_formula

theorem nativeGap074Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap074System) *ᵥ nativeVectorReal nativeGap074System.v) i ≤ nativeVectorReal nativeGap074Result i := by
  have hd := nativeGap074Domain
  have hr (i : Fin 21) : nativeGap074System.diag.getD i.val 0+nativeGap074System.subdiag.getD i.val 0+nativeGap074System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap074System.diag.getD i.val 0) (nativeGap074System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap074System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap074Taylor160] at h
  simpa only [nativeGap074Result_formula] using h

end ASDExplicitGamma.Numerics.Native
