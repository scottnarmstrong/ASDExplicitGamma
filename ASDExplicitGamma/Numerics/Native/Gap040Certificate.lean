module
public import ASDExplicitGamma.Numerics.Native.Gap040Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-40 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap040Old_source : nativeOld 40 = nativeGap040Old := by
  unfold nativeOld
  rw [nativeGap040Raw_formula]
  exact nativeGap040Old_formula

theorem nativeGap040Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap040System) *ᵥ nativeVectorReal nativeGap040System.v) i ≤ nativeVectorReal nativeGap040Result i := by
  have hd := nativeGap040Domain
  have hr (i : Fin 21) : nativeGap040System.diag.getD i.val 0+nativeGap040System.subdiag.getD i.val 0+nativeGap040System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap040System.diag.getD i.val 0) (nativeGap040System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap040System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap040Taylor160] at h
  simpa only [nativeGap040Result_formula] using h

end ASDExplicitGamma.Numerics.Native
