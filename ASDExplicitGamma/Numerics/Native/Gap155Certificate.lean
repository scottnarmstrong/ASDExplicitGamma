module
public import ASDExplicitGamma.Numerics.Native.Gap155Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-155 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap155Old_source : nativeOld 155 = nativeGap155Old := by
  unfold nativeOld
  rw [nativeGap155Raw_formula]
  exact nativeGap155Old_formula

theorem nativeGap155Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap155System) *ᵥ nativeVectorReal nativeGap155System.v) i ≤ nativeVectorReal nativeGap155Result i := by
  have hd := nativeGap155Domain
  have hr (i : Fin 21) : nativeGap155System.diag.getD i.val 0+nativeGap155System.subdiag.getD i.val 0+nativeGap155System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap155System.diag.getD i.val 0) (nativeGap155System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap155System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap155Taylor160] at h
  simpa only [nativeGap155Result_formula] using h

end ASDExplicitGamma.Numerics.Native
