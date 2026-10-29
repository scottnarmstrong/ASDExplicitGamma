module
public import ASDExplicitGamma.Numerics.Native.Gap119Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-119 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap119Old_source : nativeOld 119 = nativeGap119Old := by
  unfold nativeOld
  rw [nativeGap119Raw_formula]
  exact nativeGap119Old_formula

theorem nativeGap119Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap119System) *ᵥ nativeVectorReal nativeGap119System.v) i ≤ nativeVectorReal nativeGap119Result i := by
  have hd := nativeGap119Domain
  have hr (i : Fin 21) : nativeGap119System.diag.getD i.val 0+nativeGap119System.subdiag.getD i.val 0+nativeGap119System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap119System.diag.getD i.val 0) (nativeGap119System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap119System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap119Taylor160] at h
  simpa only [nativeGap119Result_formula] using h

end ASDExplicitGamma.Numerics.Native
