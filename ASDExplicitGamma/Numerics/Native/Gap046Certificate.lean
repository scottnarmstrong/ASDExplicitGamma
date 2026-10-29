module
public import ASDExplicitGamma.Numerics.Native.Gap046Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-46 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap046Old_source : nativeOld 46 = nativeGap046Old := by
  unfold nativeOld
  rw [nativeGap046Raw_formula]
  exact nativeGap046Old_formula

theorem nativeGap046Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap046System) *ᵥ nativeVectorReal nativeGap046System.v) i ≤ nativeVectorReal nativeGap046Result i := by
  have hd := nativeGap046Domain
  have hr (i : Fin 21) : nativeGap046System.diag.getD i.val 0+nativeGap046System.subdiag.getD i.val 0+nativeGap046System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap046System.diag.getD i.val 0) (nativeGap046System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap046System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap046Taylor160] at h
  simpa only [nativeGap046Result_formula] using h

end ASDExplicitGamma.Numerics.Native
