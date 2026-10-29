module
public import ASDExplicitGamma.Numerics.Native.Gap122Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-122 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap122Old_source : nativeOld 122 = nativeGap122Old := by
  unfold nativeOld
  rw [nativeGap122Raw_formula]
  exact nativeGap122Old_formula

theorem nativeGap122Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap122System) *ᵥ nativeVectorReal nativeGap122System.v) i ≤ nativeVectorReal nativeGap122Result i := by
  have hd := nativeGap122Domain
  have hr (i : Fin 21) : nativeGap122System.diag.getD i.val 0+nativeGap122System.subdiag.getD i.val 0+nativeGap122System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap122System.diag.getD i.val 0) (nativeGap122System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap122System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap122Taylor160] at h
  simpa only [nativeGap122Result_formula] using h

end ASDExplicitGamma.Numerics.Native
