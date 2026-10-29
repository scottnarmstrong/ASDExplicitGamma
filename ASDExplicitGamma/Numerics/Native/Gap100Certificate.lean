module
public import ASDExplicitGamma.Numerics.Native.Gap100Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-100 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap100Old_source : nativeOld 100 = nativeGap100Old := by
  unfold nativeOld
  rw [nativeGap100Raw_formula]
  exact nativeGap100Old_formula

theorem nativeGap100Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap100System) *ᵥ nativeVectorReal nativeGap100System.v) i ≤ nativeVectorReal nativeGap100Result i := by
  have hd := nativeGap100Domain
  have hr (i : Fin 21) : nativeGap100System.diag.getD i.val 0+nativeGap100System.subdiag.getD i.val 0+nativeGap100System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap100System.diag.getD i.val 0) (nativeGap100System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap100System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap100Taylor160] at h
  simpa only [nativeGap100Result_formula] using h

end ASDExplicitGamma.Numerics.Native
