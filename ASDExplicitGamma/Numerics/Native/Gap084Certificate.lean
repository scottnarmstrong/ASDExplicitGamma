module
public import ASDExplicitGamma.Numerics.Native.Gap084Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-84 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap084Old_source : nativeOld 84 = nativeGap084Old := by
  unfold nativeOld
  rw [nativeGap084Raw_formula]
  exact nativeGap084Old_formula

theorem nativeGap084Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap084System) *ᵥ nativeVectorReal nativeGap084System.v) i ≤ nativeVectorReal nativeGap084Result i := by
  have hd := nativeGap084Domain
  have hr (i : Fin 21) : nativeGap084System.diag.getD i.val 0+nativeGap084System.subdiag.getD i.val 0+nativeGap084System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap084System.diag.getD i.val 0) (nativeGap084System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap084System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap084Taylor160] at h
  simpa only [nativeGap084Result_formula] using h

end ASDExplicitGamma.Numerics.Native
