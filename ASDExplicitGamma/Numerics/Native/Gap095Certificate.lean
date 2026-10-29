module
public import ASDExplicitGamma.Numerics.Native.Gap095Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-95 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap095Old_source : nativeOld 95 = nativeGap095Old := by
  unfold nativeOld
  rw [nativeGap095Raw_formula]
  exact nativeGap095Old_formula

theorem nativeGap095Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap095System) *ᵥ nativeVectorReal nativeGap095System.v) i ≤ nativeVectorReal nativeGap095Result i := by
  have hd := nativeGap095Domain
  have hr (i : Fin 21) : nativeGap095System.diag.getD i.val 0+nativeGap095System.subdiag.getD i.val 0+nativeGap095System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap095System.diag.getD i.val 0) (nativeGap095System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap095System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap095Taylor160] at h
  simpa only [nativeGap095Result_formula] using h

end ASDExplicitGamma.Numerics.Native
