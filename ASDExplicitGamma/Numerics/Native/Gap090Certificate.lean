module
public import ASDExplicitGamma.Numerics.Native.Gap090Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-90 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap090Old_source : nativeOld 90 = nativeGap090Old := by
  unfold nativeOld
  rw [nativeGap090Raw_formula]
  exact nativeGap090Old_formula

theorem nativeGap090Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap090System) *ᵥ nativeVectorReal nativeGap090System.v) i ≤ nativeVectorReal nativeGap090Result i := by
  have hd := nativeGap090Domain
  have hr (i : Fin 21) : nativeGap090System.diag.getD i.val 0+nativeGap090System.subdiag.getD i.val 0+nativeGap090System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap090System.diag.getD i.val 0) (nativeGap090System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap090System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap090Taylor160] at h
  simpa only [nativeGap090Result_formula] using h

end ASDExplicitGamma.Numerics.Native
