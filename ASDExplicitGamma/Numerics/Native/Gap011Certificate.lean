module
public import ASDExplicitGamma.Numerics.Native.Gap011Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-11 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap011Old_source : nativeOld 11 = nativeGap011Old := by
  unfold nativeOld
  rw [nativeGap011Raw_formula]
  exact nativeGap011Old_formula

theorem nativeGap011Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap011System) *ᵥ nativeVectorReal nativeGap011System.v) i ≤ nativeVectorReal nativeGap011Result i := by
  have hd := nativeGap011Domain
  have hr (i : Fin 21) : nativeGap011System.diag.getD i.val 0+nativeGap011System.subdiag.getD i.val 0+nativeGap011System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap011System.diag.getD i.val 0) (nativeGap011System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap011System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap011Taylor160] at h
  simpa only [nativeGap011Result_formula] using h

end ASDExplicitGamma.Numerics.Native
