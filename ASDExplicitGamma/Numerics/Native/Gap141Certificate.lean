module
public import ASDExplicitGamma.Numerics.Native.Gap141Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-141 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap141Old_source : nativeOld 141 = nativeGap141Old := by
  unfold nativeOld
  rw [nativeGap141Raw_formula]
  exact nativeGap141Old_formula

theorem nativeGap141Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap141System) *ᵥ nativeVectorReal nativeGap141System.v) i ≤ nativeVectorReal nativeGap141Result i := by
  have hd := nativeGap141Domain
  have hr (i : Fin 21) : nativeGap141System.diag.getD i.val 0+nativeGap141System.subdiag.getD i.val 0+nativeGap141System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap141System.diag.getD i.val 0) (nativeGap141System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap141System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap141Taylor160] at h
  simpa only [nativeGap141Result_formula] using h

end ASDExplicitGamma.Numerics.Native
