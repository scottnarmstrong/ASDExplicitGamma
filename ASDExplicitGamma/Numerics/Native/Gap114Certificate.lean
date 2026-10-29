module
public import ASDExplicitGamma.Numerics.Native.Gap114Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-114 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap114Old_source : nativeOld 114 = nativeGap114Old := by
  unfold nativeOld
  rw [nativeGap114Raw_formula]
  exact nativeGap114Old_formula

theorem nativeGap114Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap114System) *ᵥ nativeVectorReal nativeGap114System.v) i ≤ nativeVectorReal nativeGap114Result i := by
  have hd := nativeGap114Domain
  have hr (i : Fin 21) : nativeGap114System.diag.getD i.val 0+nativeGap114System.subdiag.getD i.val 0+nativeGap114System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap114System.diag.getD i.val 0) (nativeGap114System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap114System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap114Taylor160] at h
  simpa only [nativeGap114Result_formula] using h

end ASDExplicitGamma.Numerics.Native
