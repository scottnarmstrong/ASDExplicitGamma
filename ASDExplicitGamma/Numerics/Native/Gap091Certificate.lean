module
public import ASDExplicitGamma.Numerics.Native.Gap091Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-91 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap091Old_source : nativeOld 91 = nativeGap091Old := by
  unfold nativeOld
  rw [nativeGap091Raw_formula]
  exact nativeGap091Old_formula

theorem nativeGap091Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap091System) *ᵥ nativeVectorReal nativeGap091System.v) i ≤ nativeVectorReal nativeGap091Result i := by
  have hd := nativeGap091Domain
  have hr (i : Fin 21) : nativeGap091System.diag.getD i.val 0+nativeGap091System.subdiag.getD i.val 0+nativeGap091System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap091System.diag.getD i.val 0) (nativeGap091System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap091System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap091Taylor160] at h
  simpa only [nativeGap091Result_formula] using h

end ASDExplicitGamma.Numerics.Native
