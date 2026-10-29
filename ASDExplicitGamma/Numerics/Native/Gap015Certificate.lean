module
public import ASDExplicitGamma.Numerics.Native.Gap015Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-15 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap015Old_source : nativeOld 15 = nativeGap015Old := by
  unfold nativeOld
  rw [nativeGap015Raw_formula]
  exact nativeGap015Old_formula

theorem nativeGap015Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap015System) *ᵥ nativeVectorReal nativeGap015System.v) i ≤ nativeVectorReal nativeGap015Result i := by
  have hd := nativeGap015Domain
  have hr (i : Fin 21) : nativeGap015System.diag.getD i.val 0+nativeGap015System.subdiag.getD i.val 0+nativeGap015System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap015System.diag.getD i.val 0) (nativeGap015System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap015System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap015Taylor160] at h
  simpa only [nativeGap015Result_formula] using h

end ASDExplicitGamma.Numerics.Native
