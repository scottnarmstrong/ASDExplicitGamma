module

public import ASDExplicitGamma.Inverse.FullResponseReferenceBank
public import ASDExplicitGamma.Inverse.OrderBandBounds

/-! Exact two-sided true-frame transport for the actual full response. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- Two true-frame ratios suffice for full-trace transport in either direction. -/
theorem full_response_trace_two_frame_ratios (A : BlockMat 2) (σold σ G : ℝ)
    (hold : 0 < σold) (hσ : 0 < σ) (hforward : σ/σold ≤ G) (hreverse : σold/σ ≤ G)
    (hquad : ∀ P : BlockVec 2, 0 ≤ blockVecDot P (blockMatVecMul A P)) :
    Matrix.trace (toFullBlockMat (frameMatrix σ A))/4 ≤
      G*(Matrix.trace (toFullBlockMat (frameMatrix σold A))/4) := by
  have hULdiag (j : Fin 2) : 0 ≤ A.upperLeft j j := by
    have hh := hquad (Pi.single j 1,0)
    simpa [blockVecDot,blockMatVecMul,vecDot,matVecMul,Matrix.mulVec,Fin.sum_univ_two,Pi.single_apply] using hh
  have hLRdiag (j : Fin 2) : 0 ≤ A.lowerRight j j := by
    have hh := hquad (0,Pi.single j 1)
    simpa [blockVecDot,blockMatVecMul,vecDot,matVecMul,Matrix.mulVec,Fin.sum_univ_two,Pi.single_apply] using hh
  have hUL : 0 ≤ Matrix.trace A.upperLeft := Finset.sum_nonneg fun j _ => hULdiag j
  have hLR : 0 ≤ Matrix.trace A.lowerRight := Finset.sum_nonneg fun j _ => hLRdiag j
  have hinv : σ⁻¹ ≤ G*σold⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right hreverse (inv_nonneg.mpr hold.le)
    convert hh using 1
    field_simp [hold.ne',hσ.ne']
  have hscale : σ ≤ G*σold := (div_le_iff₀ hold).mp hforward
  have hU := mul_le_mul_of_nonneg_right hinv hUL
  have hL := mul_le_mul_of_nonneg_right hscale hLR
  have he (s : ℝ) : Matrix.trace (toFullBlockMat (frameMatrix s A)) =
      s⁻¹*Matrix.trace A.upperLeft+s*Matrix.trace A.lowerRight := by
    simp [Matrix.trace,toFullBlockMat,frameMatrix,Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.diag_apply]
    ring
  rw [he σ,he σold]
  nlinarith only [hU,hL]

/-- The actual attenuated full trace is transported between arbitrary true
frames by their absolute label gap, with no extra source clock. -/
theorem full_response_trace_frame_le (M : ABKModel 2) (Q : TriadicCube 2)
    (m N K : ℤ) (hmN : m ≤ N) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    rootTraceObservable M Q m N K weights ω/4 ≤
      (3:ℝ)^(2*M.gamma*|((K-Q.scale+1:ℤ):ℝ)|)*
        (rootTraceObservable M Q m N (Q.scale-1) weights ω/4) := by
  have hforward := true_frame_ratio_le M K (Q.scale-1)
  have hreverse := true_frame_ratio_le M (Q.scale-1) K
  rw [show K-(Q.scale-1)=K-Q.scale+1 by omega] at hforward
  rw [show (Q.scale-1)-K=-(K-Q.scale+1) by omega,Int.cast_neg,abs_neg] at hreverse
  let A := coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m N weights ω)
  have hquad (P : BlockVec 2) : 0 ≤ blockVecDot P (blockMatVecMul A P) := by
    dsimp only [A]
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube]
    have hh := assembly_attenuated_domain_quadratic_nonneg M Q m m N le_rfl hmN weights ω
      (Book.Ch02.cubeDomain Q) (by intro x hx; exact hx) P
    simpa only [Book.Ch02.cubeDomain_coe] using hh
  exact full_response_trace_two_frame_ratios A _ _ _ (Annealed.sigmaBar_characterization M _).1
    (Annealed.sigmaBar_characterization M _).1 hforward hreverse hquad

/-- The norm transport uses measurability and positivity of the actual trace. -/
theorem full_response_trace_frame_Lp_le (M : ABKModel 2) (Q : TriadicCube 2)
    (m N K : ℤ) (hmN : m ≤ N) (weights : ℤ → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun ω => rootTraceObservable M Q m N K weights ω/4) p (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((K-Q.scale+1:ℤ):ℝ)|))*
        eLpNorm (fun ω => rootTraceObservable M Q m N (Q.scale-1) weights ω/4) p
          (Cutoff.cutoffSampleLaw M).toMeasure := by
  let G := (3:ℝ)^(2*M.gamma*|((K-Q.scale+1:ℤ):ℝ)|)
  let F := fun ω => rootTraceObservable M Q m N (Q.scale-1) weights ω/4
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hm := (root_trace_observable_measurable M Q m N K weights).div_const 4
  have hmono : eLpNorm (fun ω => rootTraceObservable M Q m N K weights ω/4) p (Cutoff.cutoffSampleLaw M).toMeasure ≤
      eLpNorm (G • F) p (Cutoff.cutoffSampleLaw M).toMeasure := by
    apply eLpNorm_mono_ae_real hm.aestronglyMeasurable
    filter_upwards with ω
    have hnonneg : 0 ≤ rootTraceObservable M Q m N K weights ω/4 :=
      div_nonneg (root_trace_observable_nonneg M Q m N K hmN weights ω) (by norm_num)
    rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
    exact full_response_trace_frame_le M Q m N K hmN weights ω
  rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hG] at hmono
  exact hmono

end
end ASDExplicitGamma.Inverse
