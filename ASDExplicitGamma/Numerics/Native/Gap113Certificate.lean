module
public import ASDExplicitGamma.Numerics.Native.Gap113Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-113 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap113Old_source : nativeOld 113 = nativeGap113Old := by
  unfold nativeOld
  rw [nativeGap113Raw_formula]
  exact nativeGap113Old_formula

theorem nativeGap113Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap113System) *ᵥ nativeVectorReal nativeGap113System.v) i ≤ nativeVectorReal nativeGap113Result i := by
  have hd := nativeGap113Domain
  have hr (i : Fin 21) : nativeGap113System.diag.getD i.val 0+nativeGap113System.subdiag.getD i.val 0+nativeGap113System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap113System.diag.getD i.val 0) (nativeGap113System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap113System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap113Taylor160] at h
  simpa only [nativeGap113Result_formula] using h

end ASDExplicitGamma.Numerics.Native
