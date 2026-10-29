module
public import ASDExplicitGamma.Numerics.Native.Gap073Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-73 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap073Old_source : nativeOld 73 = nativeGap073Old := by
  unfold nativeOld
  rw [nativeGap073Raw_formula]
  exact nativeGap073Old_formula

theorem nativeGap073Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap073System) *ᵥ nativeVectorReal nativeGap073System.v) i ≤ nativeVectorReal nativeGap073Result i := by
  have hd := nativeGap073Domain
  have hr (i : Fin 21) : nativeGap073System.diag.getD i.val 0+nativeGap073System.subdiag.getD i.val 0+nativeGap073System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap073System.diag.getD i.val 0) (nativeGap073System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap073System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap073Taylor160] at h
  simpa only [nativeGap073Result_formula] using h

end ASDExplicitGamma.Numerics.Native
