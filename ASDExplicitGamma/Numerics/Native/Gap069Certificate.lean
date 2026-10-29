module
public import ASDExplicitGamma.Numerics.Native.Gap069Taylor
public import ASDExplicitGamma.Numerics.Native.MatrixReplay
/-! Real exponential enclosure for the complete configured gap-69 system. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

theorem nativeGap069Old_source : nativeOld 69 = nativeGap069Old := by
  unfold nativeOld
  rw [nativeGap069Raw_formula]
  exact nativeGap069Old_formula

theorem nativeGap069Exp_bound : ∀ i : Fin 21,
    (NormedSpace.exp (nativeSystemMatrix nativeGap069System) *ᵥ nativeVectorReal nativeGap069System.v) i ≤ nativeVectorReal nativeGap069Result i := by
  have hd := nativeGap069Domain
  have hr (i : Fin 21) : nativeGap069System.diag.getD i.val 0+nativeGap069System.subdiag.getD i.val 0+nativeGap069System.force.getD i.val 0 ≤ 6 := by
    rw [add_comm (nativeGap069System.diag.getD i.val 0) (nativeGap069System.subdiag.getD i.val 0)]
    exact hd.2.2.2 i
  have h := nativeTaylor_replay_sound nativeGap069System (by decide +kernel)
    (fun i => (hd.2.2.1 i).1) (fun i => (hd.2.1 i).1)
    (fun i => (hd.2.2.1 i).2.1) hr hd.1
  rw [nativeGap069Taylor160] at h
  simpa only [nativeGap069Result_formula] using h

end ASDExplicitGamma.Numerics.Native
