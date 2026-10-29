module
public import ASDExplicitGamma.Numerics.Native.Gap070Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-70 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap070Old_source : nativeOld 70 = nativeGap070Old := by
  unfold nativeOld
  rw [nativeGap070Raw_formula]
  exact nativeGap070Old_formula

theorem nativeGap070Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap070System) *ᵥ nativeVectorReal nativeGap070System.v) i ≤ nativeVectorReal nativeGap070Result i := by
  have hd := nativeGap070Domain
  have hr (i : Fin 21) : nativeGap070System.diag.getD i.val 0+nativeGap070System.subdiag.getD i.val 0+nativeGap070System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap070System.diag.getD i.val 0) (nativeGap070System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap070System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap070Taylor160] at h
  simpa only [nativeGap070Result_formula] using h

end ASDExplicitGamma.Numerics.Native
