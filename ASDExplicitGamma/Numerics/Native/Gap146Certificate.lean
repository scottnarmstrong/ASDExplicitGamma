module
public import ASDExplicitGamma.Numerics.Native.Gap146Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-146 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap146Old_source : nativeOld 146 = nativeGap146Old := by
  unfold nativeOld
  rw [nativeGap146Raw_formula]
  exact nativeGap146Old_formula

theorem nativeGap146Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap146System) *ᵥ nativeVectorReal nativeGap146System.v) i ≤ nativeVectorReal nativeGap146Result i := by
  have hd := nativeGap146Domain
  have hr (i : Fin 21) : nativeGap146System.diag.getD i.val 0+nativeGap146System.subdiag.getD i.val 0+nativeGap146System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap146System.diag.getD i.val 0) (nativeGap146System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap146System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap146Taylor160] at h
  simpa only [nativeGap146Result_formula] using h

end ASDExplicitGamma.Numerics.Native
