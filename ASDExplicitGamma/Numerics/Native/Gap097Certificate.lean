module
public import ASDExplicitGamma.Numerics.Native.Gap097Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-97 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap097Old_source : nativeOld 97 = nativeGap097Old := by
  unfold nativeOld
  rw [nativeGap097Raw_formula]
  exact nativeGap097Old_formula

theorem nativeGap097Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap097System) *ᵥ nativeVectorReal nativeGap097System.v) i ≤ nativeVectorReal nativeGap097Result i := by
  have hd := nativeGap097Domain
  have hr (i : Fin 21) : nativeGap097System.diag.getD i.val 0+nativeGap097System.subdiag.getD i.val 0+nativeGap097System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap097System.diag.getD i.val 0) (nativeGap097System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap097System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap097Taylor160] at h
  simpa only [nativeGap097Result_formula] using h

end ASDExplicitGamma.Numerics.Native
