module
public import ASDExplicitGamma.Numerics.Native.Gap092Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-92 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap092Old_source : nativeOld 92 = nativeGap092Old := by
  unfold nativeOld
  rw [nativeGap092Raw_formula]
  exact nativeGap092Old_formula

theorem nativeGap092Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap092System) *ᵥ nativeVectorReal nativeGap092System.v) i ≤ nativeVectorReal nativeGap092Result i := by
  have hd := nativeGap092Domain
  have hr (i : Fin 21) : nativeGap092System.diag.getD i.val 0+nativeGap092System.subdiag.getD i.val 0+nativeGap092System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap092System.diag.getD i.val 0) (nativeGap092System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap092System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap092Taylor160] at h
  simpa only [nativeGap092Result_formula] using h

end ASDExplicitGamma.Numerics.Native
