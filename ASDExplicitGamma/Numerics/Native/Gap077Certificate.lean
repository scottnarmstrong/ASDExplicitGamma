module
public import ASDExplicitGamma.Numerics.Native.Gap077Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-77 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap077Old_source : nativeOld 77 = nativeGap077Old := by
  unfold nativeOld
  rw [nativeGap077Raw_formula]
  exact nativeGap077Old_formula

theorem nativeGap077Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap077System) *ᵥ nativeVectorReal nativeGap077System.v) i ≤ nativeVectorReal nativeGap077Result i := by
  have hd := nativeGap077Domain
  have hr (i : Fin 21) : nativeGap077System.diag.getD i.val 0+nativeGap077System.subdiag.getD i.val 0+nativeGap077System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap077System.diag.getD i.val 0) (nativeGap077System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap077System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap077Taylor160] at h
  simpa only [nativeGap077Result_formula] using h

end ASDExplicitGamma.Numerics.Native
