module
public import ASDExplicitGamma.Numerics.Native.Gap089Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-89 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap089Old_source : nativeOld 89 = nativeGap089Old := by
  unfold nativeOld
  rw [nativeGap089Raw_formula]
  exact nativeGap089Old_formula

theorem nativeGap089Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap089System) *ᵥ nativeVectorReal nativeGap089System.v) i ≤ nativeVectorReal nativeGap089Result i := by
  have hd := nativeGap089Domain
  have hr (i : Fin 21) : nativeGap089System.diag.getD i.val 0+nativeGap089System.subdiag.getD i.val 0+nativeGap089System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap089System.diag.getD i.val 0) (nativeGap089System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap089System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap089Taylor160] at h
  simpa only [nativeGap089Result_formula] using h

end ASDExplicitGamma.Numerics.Native
