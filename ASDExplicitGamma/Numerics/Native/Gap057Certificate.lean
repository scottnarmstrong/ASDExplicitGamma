module
public import ASDExplicitGamma.Numerics.Native.Gap057Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-57 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap057Old_source : nativeOld 57 = nativeGap057Old := by
  unfold nativeOld
  rw [nativeGap057Raw_formula]
  exact nativeGap057Old_formula

theorem nativeGap057Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap057System) *ᵥ nativeVectorReal nativeGap057System.v) i ≤ nativeVectorReal nativeGap057Result i := by
  have hd := nativeGap057Domain
  have hr (i : Fin 21) : nativeGap057System.diag.getD i.val 0+nativeGap057System.subdiag.getD i.val 0+nativeGap057System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap057System.diag.getD i.val 0) (nativeGap057System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap057System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap057Taylor160] at h
  simpa only [nativeGap057Result_formula] using h

end ASDExplicitGamma.Numerics.Native
