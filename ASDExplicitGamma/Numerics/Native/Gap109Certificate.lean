module
public import ASDExplicitGamma.Numerics.Native.Gap109Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-109 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap109Old_source : nativeOld 109 = nativeGap109Old := by
  unfold nativeOld
  rw [nativeGap109Raw_formula]
  exact nativeGap109Old_formula

theorem nativeGap109Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap109System) *ᵥ nativeVectorReal nativeGap109System.v) i ≤ nativeVectorReal nativeGap109Result i := by
  have hd := nativeGap109Domain
  have hr (i : Fin 21) : nativeGap109System.diag.getD i.val 0+nativeGap109System.subdiag.getD i.val 0+nativeGap109System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap109System.diag.getD i.val 0) (nativeGap109System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap109System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap109Taylor160] at h
  simpa only [nativeGap109Result_formula] using h

end ASDExplicitGamma.Numerics.Native
