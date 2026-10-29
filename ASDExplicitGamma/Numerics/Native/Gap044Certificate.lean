module
public import ASDExplicitGamma.Numerics.Native.Gap044Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-44 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap044Old_source : nativeOld 44 = nativeGap044Old := by
  unfold nativeOld
  rw [nativeGap044Raw_formula]
  exact nativeGap044Old_formula

theorem nativeGap044Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap044System) *ᵥ nativeVectorReal nativeGap044System.v) i ≤ nativeVectorReal nativeGap044Result i := by
  have hd := nativeGap044Domain
  have hr (i : Fin 21) : nativeGap044System.diag.getD i.val 0+nativeGap044System.subdiag.getD i.val 0+nativeGap044System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap044System.diag.getD i.val 0) (nativeGap044System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap044System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap044Taylor160] at h
  simpa only [nativeGap044Result_formula] using h

end ASDExplicitGamma.Numerics.Native
