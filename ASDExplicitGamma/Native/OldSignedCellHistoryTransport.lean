module

public import ASDExplicitGamma.Native.OldSignedCellMaxHistoryMoment

/-! Actual evolving OLD history bounds uniformly over the source cells. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Transport on every source cell with the theta-scaled full64 slope. -/
theorem old_signed_cell_full64_max_history_transport
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l)
    (Q : TriadicCube 2) (hQ : Q.scale = n-5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    eLpNorm (Main.mainOrdinaryTraceMaxHistory M n Q t)
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*((coldHistoryBeta^5)⁻¹*(2379/2500)+(49/100)*t)) := by
  let B := fun j : ℕ => lpNorm (rawDepthFourLoadTrace M n (n-((5+j:ℕ):ℤ)) 0)
    20 (Cutoff.cutoffSampleLaw M).toMeasure
  let U := oldSignedP20Full64Control M h n
  have hinit := old_signed_shifted_strong_profile M n 5 _
    (mul_nonneg (by norm_num : (0:ℝ)≤2379/2500) (cold_theta_pos M).le) (hpast n le_rfl).2.1
  have hBsum : Summable (fun j => coldHistoryBeta^j*B j) := by
    simpa only [B,Main.main_rawDepthFourLoadTrace_lpNorm_twenty_zero_eq_cutoff] using hinit.1
  have hUsum := old_signed_full64_slope_sum M h n hg (hpast n le_rfl)
  have hsum : Summable (fun j => coldHistoryBeta^j*(B j+t*U j)) := by
    have hh := hBsum.add (hUsum.1.mul_left t)
    apply hh.congr
    intro j
    dsimp [U]
    ring
  have hnonneg (j : ℕ) : 0≤B j+t*U j := add_nonneg lpNorm_nonneg
    (mul_nonneg ht.1 (old_signed_full64_control_nonneg M h n j))
  have hh := old_signed_cell_max_history_moment_of_profile M h hM hg n hpast Q hQ t ht
    (fun j => B j+t*U j) hnonneg hsum
    (old_signed_full64_depth_trace_transport M h hM hg n hpast · t ht)
  apply hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have he : (∑' j : ℕ,coldHistoryBeta^j*(B j+t*U j))=
      (∑' j : ℕ,coldHistoryBeta^j*B j)+t*(∑' j : ℕ,coldHistoryBeta^j*U j) := by
    calc
      _ = ∑' j : ℕ,(coldHistoryBeta^j*B j+t*(coldHistoryBeta^j*U j)) := by
        apply tsum_congr
        intro j
        ring
      _ = _ := by rw [hBsum.tsum_add (hUsum.1.mul_left t),tsum_mul_left]
  rw [he]
  have hi := old_signed_initial_q1_profile M h n (hpast n le_rfl)
  have htU := mul_le_mul_of_nonneg_left hUsum.2 ht.1
  dsimp only [B,U] at *
  nlinarith only [hi,htU]

end
end ASDExplicitGamma.Native
