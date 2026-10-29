module
public import ASDExplicitGamma.Numerics.Native.Gap016Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-16 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap016Old_source : nativeOld 16 = nativeGap016Old := by
  unfold nativeOld
  rw [nativeGap016Raw_formula]
  exact nativeGap016Old_formula

theorem nativeGap016Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap016System) *ᵥ nativeVectorReal nativeGap016System.v) i ≤ nativeVectorReal nativeGap016Result i := by
  have hd := nativeGap016Domain
  have hr (i : Fin 21) : nativeGap016System.diag.getD i.val 0+nativeGap016System.subdiag.getD i.val 0+nativeGap016System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap016System.diag.getD i.val 0) (nativeGap016System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap016System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap016Taylor160] at h
  simpa only [nativeGap016Result_formula] using h

end ASDExplicitGamma.Numerics.Native
