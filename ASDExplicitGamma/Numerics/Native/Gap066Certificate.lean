module
public import ASDExplicitGamma.Numerics.Native.Gap066Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-66 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap066Old_source : nativeOld 66 = nativeGap066Old := by
  unfold nativeOld
  rw [nativeGap066Raw_formula]
  exact nativeGap066Old_formula

theorem nativeGap066Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap066System) *ᵥ nativeVectorReal nativeGap066System.v) i ≤ nativeVectorReal nativeGap066Result i := by
  have hd := nativeGap066Domain
  have hr (i : Fin 21) : nativeGap066System.diag.getD i.val 0+nativeGap066System.subdiag.getD i.val 0+nativeGap066System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap066System.diag.getD i.val 0) (nativeGap066System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap066System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap066Taylor160] at h
  simpa only [nativeGap066Result_formula] using h

end ASDExplicitGamma.Numerics.Native
