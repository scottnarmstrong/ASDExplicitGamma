module
public import ASDExplicitGamma.Numerics.Native.Gap094Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-94 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap094Old_source : nativeOld 94 = nativeGap094Old := by
  unfold nativeOld
  rw [nativeGap094Raw_formula]
  exact nativeGap094Old_formula

theorem nativeGap094Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap094System) *ᵥ nativeVectorReal nativeGap094System.v) i ≤ nativeVectorReal nativeGap094Result i := by
  have hd := nativeGap094Domain
  have hr (i : Fin 21) : nativeGap094System.diag.getD i.val 0+nativeGap094System.subdiag.getD i.val 0+nativeGap094System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap094System.diag.getD i.val 0) (nativeGap094System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap094System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap094Taylor160] at h
  simpa only [nativeGap094Result_formula] using h

end ASDExplicitGamma.Numerics.Native
