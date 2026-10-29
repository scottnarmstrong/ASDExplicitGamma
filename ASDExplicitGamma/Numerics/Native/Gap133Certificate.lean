module
public import ASDExplicitGamma.Numerics.Native.Gap133Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-133 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap133Old_source : nativeOld 133 = nativeGap133Old := by
  unfold nativeOld
  rw [nativeGap133Raw_formula]
  exact nativeGap133Old_formula

theorem nativeGap133Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap133System) *ᵥ nativeVectorReal nativeGap133System.v) i ≤ nativeVectorReal nativeGap133Result i := by
  have hd := nativeGap133Domain
  have hr (i : Fin 21) : nativeGap133System.diag.getD i.val 0+nativeGap133System.subdiag.getD i.val 0+nativeGap133System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap133System.diag.getD i.val 0) (nativeGap133System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap133System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap133Taylor160] at h
  simpa only [nativeGap133Result_formula] using h

end ASDExplicitGamma.Numerics.Native
