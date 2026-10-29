module
public import ASDExplicitGamma.Numerics.Native.Gap156Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-156 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap156Old_source : nativeOld 156 = nativeGap156Old := by
  unfold nativeOld
  rw [nativeGap156Raw_formula]
  exact nativeGap156Old_formula

theorem nativeGap156Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap156System) *ᵥ nativeVectorReal nativeGap156System.v) i ≤ nativeVectorReal nativeGap156Result i := by
  have hd := nativeGap156Domain
  have hr (i : Fin 21) : nativeGap156System.diag.getD i.val 0+nativeGap156System.subdiag.getD i.val 0+nativeGap156System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap156System.diag.getD i.val 0) (nativeGap156System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap156System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap156Taylor160] at h
  simpa only [nativeGap156Result_formula] using h

end ASDExplicitGamma.Numerics.Native
