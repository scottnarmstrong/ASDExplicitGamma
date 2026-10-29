module

public import ASDExplicitGamma.Scalar.CombineExp
public import ASDExplicitGamma.Scalar.ResolventCombine

/-! The combine theorem for the actual NEW-resolvent quartic: `∫ Qt ≤ vol (amp²)² C♯(Fflat, Fdef)`
and the paid one-shell charge. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

/-- Optimization of the AM-GM parameter. -/
theorem inf_amgm {S K F G : ℝ} (hK : 0 ≤ K) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (h : ∀ t : ℝ, 0 < t → S ≤ K * ((141 / 100 : ℝ) * (t * F + G / t))) :
    S ≤ K * ((141 / 50 : ℝ) * Real.sqrt (F * G)) := by
  set sF := Real.sqrt F with hsF
  set sG := Real.sqrt G with hsG
  have hF2 : sF ^ 2 = F := Real.sq_sqrt hF
  have hG2 : sG ^ 2 = G := Real.sq_sqrt hG
  have hsq : Real.sqrt (F * G) = sF * sG := Real.sqrt_mul hF G
  have hsF0 : 0 ≤ sF := Real.sqrt_nonneg _
  have hsG0 : 0 ≤ sG := Real.sqrt_nonneg _
  have key : ∀ δ : ℝ, 0 < δ → S ≤ K * ((141 / 50 : ℝ) * ((sF + δ) * (sG + δ))) := by
    intro δ hδ
    have ha : 0 < sF + δ := by linarith
    have hb : 0 < sG + δ := by linarith
    have ht : 0 < (sG + δ) / (sF + δ) := div_pos hb ha
    have h1 := h _ ht
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hK)
    have h2 : (sG + δ) / (sF + δ) * F + G / ((sG + δ) / (sF + δ)) ≤ 2 * ((sF + δ) * (sG + δ)) := by
      rw [← hF2, ← hG2]
      have e1 : (sG + δ) / (sF + δ) * sF ^ 2 ≤ (sG + δ) / (sF + δ) * (sF + δ) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsF0 (by linarith) 2) ht.le
      have e2 : sG ^ 2 / ((sG + δ) / (sF + δ)) ≤ (sG + δ) ^ 2 / ((sG + δ) / (sF + δ)) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ hsG0 (by linarith) 2) ht.le
      have e3 : (sG + δ) / (sF + δ) * (sF + δ) ^ 2 + (sG + δ) ^ 2 / ((sG + δ) / (sF + δ)) =
          2 * ((sF + δ) * (sG + δ)) := by
        field_simp
        ring
      linarith
    nlinarith [h2]
  have hlim : Tendsto (fun δ : ℝ => K * ((141 / 50 : ℝ) * ((sF + δ) * (sG + δ)))) (𝓝[>] 0)
      (𝓝 (K * ((141 / 50 : ℝ) * ((sF + 0) * (sG + 0))))) := by
    have hc : Continuous (fun δ : ℝ => K * ((141 / 50 : ℝ) * ((sF + δ) * (sG + δ)))) := by
      fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have := ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ => key δ hδ)
  rw [hsq]
  simpa using this

theorem defectFdefR_nonneg (a5 ξ mStar : ℝ) :
    0 ≤ defectFdefR a5 ξ mStar (14103 / 10000)
      (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24) roughR := by
  unfold defectFdefR defectLambda roughR defectA
  positivity

section Main

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

/-- **COMBINE** (SC-NEW-RESOLVENT-COMBINE), pathwise-expectation form: the actual NEW quartic
`⟪J s₂, N s₂⟫` is bounded in expectation by `vol (amp²)² C♯(Fflat, Fdef)`. -/
theorem sc_new_resolvent_combine_core (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (he : Book.Ch02.vecNorm e = 1)
    (he2 : vecNormSq e = 1) {Fflat : ℝ}
    (hF : FlatExpectationBound M h m hab hcd hQ e Fflat) :
    ∫ ω, ⟪(CC).Jop ((CC).s2R m ω), (CC).Nop m ω ((CC).s2R m ω)⟫_ℝ
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (volume (openCubeSet (originCube 2 (m + 129)))).toReal * (((CC).amp ^ 2) ^ 2 *
        newResolventCSharp Fflat (defectFdefR mainSourceMeanPrefix (xi'' M h m)
          (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24)
          roughR)) := by
  set μ := (Cutoff.cutoffSampleLaw M).toMeasure with hμ
  set vol := (volume (openCubeSet (originCube 2 (m + 129)))).toReal with hvol
  set Fd := defectFdefR mainSourceMeanPrefix (xi'' M h m)
          (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24)
          roughR with hFd
  have hvol0 : 0 ≤ vol := ENNReal.toReal_nonneg
  have hFd0 : 0 ≤ Fd := defectFdefR_nonneg _ _ _
  have hF0 := hF.1
  have hFi := hF.2.2.1
  have hFb := hF.2.2.2
  set P := flatMajorant M h m hab hcd hQ e with hP
  have hP0 := flatMajorant_nonneg M h m hab hcd hQ e
  set A2 := ((CC).amp ^ 2) ^ 2 with hA2
  have hA20 : 0 ≤ A2 := sq_nonneg _
  have hRHS0 : 0 ≤ vol * (A2 * newResolventCSharp Fflat Fd) := by
    unfold newResolventCSharp
    positivity
  by_cases hint : Integrable (fun ω => ⟪(CC).Jop ((CC).s2R m ω), (CC).Nop m ω ((CC).s2R m ω)⟫_ℝ) μ
  swap
  · rw [integral_undef hint]; exact hRHS0
  -- defect leg
  obtain ⟨hDi, hDb⟩ := sc_new_resolvent_defect_nodeRR M h m hab hcd hQ e hM hγ hpast he he2
  -- cross leg
  have hcrossT := fun t (ht : 0 < t) => cross_expect_t M h m hab hcd hQ e hM hγ hpast he he2 hF ht
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact (closedRectangle a b c d)
    (closedRectangle_isCompact a b c d)
  have hcm : Measurable (fun ω : Cutoff.CutoffSample 2 => 2 * (CC).crossActR m ω) :=
    ((CC).crossActR_measurable m ell hK).const_mul 2
  have hcInt : Integrable (fun ω => max (2 * (CC).crossActR m ω) 0) μ :=
    (hcrossT 1 one_pos).1
  have hcB : ∫ ω, max (2 * (CC).crossActR m ω) 0 ∂μ ≤ vol * (A2 * ((141 / 50 : ℝ) *
      Real.sqrt (Fflat * Fd))) := by
    have := inf_amgm (S := ∫ ω, max (2 * (CC).crossActR m ω) 0 ∂μ)
      (K := vol * A2) (F := Fflat) (G := Fd) (by positivity) hF0 hFd0 (fun t ht => by
        have := (hcrossT t ht).2
        calc _ ≤ _ := this
          _ = _ := by ring)
    calc _ ≤ _ := this
      _ = _ := by ring
  -- pathwise
  have hpt : ∀ ω, ⟪(CC).Jop ((CC).s2R m ω), (CC).Nop m ω ((CC).s2R m ω)⟫_ℝ ≤
      vol * P ω + max (2 * (CC).crossActR m ω) 0 + max ((CC).DactR m ω) 0 := by
    intro ω
    rw [Cfg''.quartic_expand]
    have hd := Cfg''.aR_diag_le M h m hab hcd hQ e ω (Cfg''.flatCellAdm m hab hcd hQ e ω)
    have hd' : ⟪(CC).Jop ((CC).aR m ω), (CC).Nop m ω ((CC).aR m ω)⟫_ℝ ≤ vol * P ω := by
      refine hd.trans (le_of_eq ?_)
      simp only [hP, flatMajorant, hvol]
      ring
    have h1 := le_max_left (2 * (CC).crossActR m ω) 0
    have h2 := le_max_left ((CC).DactR m ω) 0
    rw [show ⟪(CC).Jop ((CC).sDefR m ω), (CC).Nop m ω ((CC).aR m ω)⟫_ℝ = (CC).crossActR m ω from rfl,
      show ⟪(CC).Jop ((CC).sDefR m ω), (CC).Nop m ω ((CC).sDefR m ω)⟫_ℝ = (CC).DactR m ω from rfl]
    linarith
  have i1 : Integrable (fun ω => vol * P ω) μ := hFi.const_mul vol
  have i12 : Integrable (fun ω => vol * P ω + max (2 * (CC).crossActR m ω) 0) μ :=
    i1.add hcInt
  have hgInt : Integrable (fun ω => vol * P ω + max (2 * (CC).crossActR m ω) 0 +
      max ((CC).DactR m ω) 0) μ := i12.add hDi
  have h3 := integral_mono hint hgInt hpt
  rw [integral_add i12 hDi, integral_add i1 hcInt, integral_const_mul] at h3
  have h4 : vol * ∫ ω, P ω ∂μ ≤ vol * (A2 * Fflat) := mul_le_mul_of_nonneg_left hFb hvol0
  refine h3.trans ?_
  have hDb' : ∫ ω, max ((CC).DactR m ω) 0 ∂μ ≤ vol * (A2 * ((44 / 25 : ℝ) * Fd)) := by
    calc _ ≤ _ := hDb
      _ = _ := by ring
  unfold newResolventCSharp
  have := add_le_add (add_le_add h4 hcB) hDb'
  refine this.trans (le_of_eq ?_)
  ring

end Main

end

end ASDExplicitGamma.Scalar
