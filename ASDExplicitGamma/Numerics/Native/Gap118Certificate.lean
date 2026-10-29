module
public import ASDExplicitGamma.Numerics.Native.Gap118Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-118 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap118Old_source : nativeOld 118 = nativeGap118Old := by
  unfold nativeOld
  rw [nativeGap118Raw_formula]
  exact nativeGap118Old_formula

theorem nativeGap118Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap118System) *ᵥ nativeVectorReal nativeGap118System.v) i ≤ nativeVectorReal nativeGap118Result i := by
  have hd := nativeGap118Domain
  have hr (i : Fin 21) : nativeGap118System.diag.getD i.val 0+nativeGap118System.subdiag.getD i.val 0+nativeGap118System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap118System.diag.getD i.val 0) (nativeGap118System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap118System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap118Taylor160] at h
  simpa only [nativeGap118Result_formula] using h

end ASDExplicitGamma.Numerics.Native
