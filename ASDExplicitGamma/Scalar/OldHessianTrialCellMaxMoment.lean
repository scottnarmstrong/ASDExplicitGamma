module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellMaxTrace

/-! Sharp completed source maximum-history moments from the genuine strong20 cap. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Every actual fine cell retains theta Hsrc in its full L20 maximum
history, with the complete population payment made before the moment. -/
theorem old_hessian_cell_max_trace_L20
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134) :
    eLpNorm (oldHessianCellMaxTraceHistory M m U) 20 (Cutoff.cutoffSampleLaw M).toMeasure≤
      ENNReal.ofReal (theta M*(5423/2500:ℝ)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let S := (2379/2500:ℝ)*theta M
  let B := fun j : ℕ => lpNorm (rawDepthFourLoadTrace M m (m-((5+j:ℕ):ℤ)) 0) 20 μ
  have hθ := (cold_theta_pos M).le
  have hS : 0≤S := mul_nonneg (by norm_num) hθ
  have hstate := hpast m hm
  have hstrong := old_signed_shifted_strong_profile M m 5 S hS hstate.2.1
  have hBs : Summable (fun j => coldHistoryBeta^j*B j) := by
    dsimp only [B,μ]
    simp_rw [Main.main_rawDepthFourLoadTrace_lpNorm_twenty_zero_eq_cutoff]
    exact hstrong.1
  have hscale : U.scale=m-5 := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
    change U.scale=m+129-134 at hs
    omega
  have hraw := old_signed_cell_max_history_moment_of_profile M h hM hg m
    (fun l hl => hpast l (hl.trans_lt hm)) U hscale 0 (by norm_num) B (fun _ => lpNorm_nonneg) hBs (fun _ => le_rfl)
  have hcost := old_signed_initial_q1_profile M h m hstate
  have hb0 := pow_pos coldHistoryBeta_pos 5
  have hsmall : (coldHistoryBeta^5)⁻¹*S≤theta M*(5423/2500:ℝ) := by
    calc
      _ = S/(coldHistoryBeta^5) := by ring
      _ ≤ _ := (div_le_iff₀ hb0).2 (by
        have hh := mul_le_mul_of_nonneg_right (old_hessian_strong_weight_cap 5 (by norm_num)) hθ
        dsimp only [S]
        convert hh using 1 <;> ring)
  have hcap : (1-inverseHistoryDiscount)*(∑' j : ℕ,coldHistoryBeta^j*B j)≤theta M*(5423/2500:ℝ) :=
    hcost.trans hsmall
  have hnormRaw := hraw.trans (ENNReal.ofReal_le_ofReal hcap)
  have he : (fun ω => ENNReal.ofReal (oldHessianCellMaxTraceHistory M m U ω))=
      mainOrdinaryTraceMaxHistory M m U 0 := by
    funext ω
    exact (old_hessian_cell_max_trace_history M m U hU ω).symm
  calc
    _ = eLpNorm (fun ω => ENNReal.ofReal (oldHessianCellMaxTraceHistory M m U ω)) 20 μ :=
      (eLpNorm_ofReal _ (Filter.Eventually.of_forall (old_hessian_cell_max_trace_nonneg M m U hU))).symm
    _ ≤ _ := by rw [he]; exact hnormRaw

/-- The same physical real history has genuine L2 membership and its
sharp theta-scaled norm cap, ready for the matrix/corrector moments. -/
theorem old_hessian_cell_max_trace_L2
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134) :
    MemLp (oldHessianCellMaxTraceHistory M m U) 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (oldHessianCellMaxTraceHistory M m U) 2 (Cutoff.cutoffSampleLaw M).toMeasure≤
        theta M*(5423/2500:ℝ) := by
  have h20 := old_hessian_cell_max_trace_L20 M h hM hg N hpast m hm U hU
  have h2 : eLpNorm (oldHessianCellMaxTraceHistory M m U) 2 (Cutoff.cutoffSampleLaw M).toMeasure≤
      ENNReal.ofReal (theta M*(5423/2500:ℝ)) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2:ℝ≥0∞)≤20)).trans h20
  have hnon : 0≤theta M*(5423/2500:ℝ) := mul_nonneg (cold_theta_pos M).le (by norm_num)
  refine ⟨h2.trans_lt ENNReal.ofReal_lt_top,?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rw [ENNReal.toReal_ofReal hnon] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
