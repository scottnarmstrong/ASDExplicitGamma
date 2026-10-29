module

public import ASDExplicitGamma.Main.ThetaGeneratorScaleTerms
public import ASDExplicitGamma.Main.ThetaGeneratorObsNodes
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeASlope
public import ASDExplicitGamma.Main.ObsChronologyMonotone

/-! MA-THETA-CONTINUATION, unconditional core: for `0 < γ ≤ γ₀`, `θ = γ/γ₀`, the observer trace
heat average `f` satisfies, a.e. on `[0,1]`,
`f' ≤ θ · [ v̄ q + aff_{γ₀}(t) + E_{γ₀}(f/θ) + I_abs,γ₀(t) ]` with `v̄ = mainSourceClock γ₀`
and `f/θ` in the `v̄`-domain at `γ₀`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Inverse
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

theorem ma_theta_generator_observer_node
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (hobs : ℕ) (h1 : 1 ≤ hobs) (h40 : hobs ≤ 40) :
    let q := mainAffineFlatBoundaryCapQ (hobs - 1)
    let vbar := mainSourceClock gammaZero
    let f := modelTraceHeatAverage (m + (hobs : ℤ)) M m
    AbsolutelyContinuousOnInterval f 0 1 ∧
      (∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f s / theta M ∧
        f s / theta M ≤
          min (mainEnvelopeA vbar gammaZero mainSourceMeanPrefix s)
            (mainEnvelopeXi vbar gammaZero mainSourceInversePrefix 1 s / mainBetaOld)) ∧
      (∀ᵐ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        deriv f s ≤ theta M * (vbar * q + mainAffineTermGamma0 q s +
          mainSourceError' vbar (mainEnvelopeA vbar gammaZero mainSourceMeanPrefix s)
            (f s / theta M) (mainEnvelopeH35 vbar gammaZero s)
            (mainEnvelopeXi vbar gammaZero mainSourceInversePrefix 1 s) q +
          mainInverseAbs vbar (mainInverseMuMinusSource vbar) s)) := by
  intro q vbar f
  have hnode := ma_generator_hypotheses_observer_node_Th M h hM hγ N hpast m hm hobs
    h1 h40
  dsimp only at hnode
  have hgpos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hz : (0 : ℝ) < gammaZero := by norm_num [gammaZero]
  have hθdef : theta M = M.gamma / gammaZero := rfl
  have hθpos : 0 < theta M := by rw [hθdef]; positivity
  have hθ1 : theta M ≤ 1 := by rw [hθdef, div_le_one hz]; exact hγ
  have hvbar : 0 ≤ vbar := (mainSourceClock_pos hz).le
  have hq : 0 ≤ q := chrono_capQ_nonneg _
  set b := q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ) with hbdef
  have hv0 : 0 ≤ b ^ 2 := sq_nonneg b
  have hb : b ^ 2 ≤ theta M * vbar := by
    have h1 := chrono_v_le_clock M h m hgpos (hpast m hm)
    have h2 := th_clock_le hgpos hγ
    rw [hθdef]; exact h1.trans h2
  have hbo : 0 < mainBetaOld := by unfold mainBetaOld; norm_num
  have hμ := th_mu_scale_le (w := vbar) hθpos.le hθ1 hgpos.le hγ hv0 hvbar hb
  have hχ := th_chi_scale_le (w := vbar) hθpos.le hθ1 hgpos.le hγ le_rfl hv0 hvbar hb
  have hpre : 0 ≤ mainSourceMeanPrefix := by
    have := mainSourceMeanPrefix_gate; linarith
  have hbsq : b ^ 2 = (q3ModelAmplitude M h (m + 1)) ^ 2 / (Annealed.sigmaBar M m : ℝ) ^ 2 := by
    rw [hbdef, div_pow]
  have hAenv (s : ℝ) (hs : 0 ≤ s) :
      mainEnvelopeA (b ^ 2) M.gamma (theta M * mainSourceMeanPrefix) s ≤
        theta M * mainEnvelopeA vbar gammaZero mainSourceMeanPrefix s := by
    unfold mainEnvelopeA
    nlinarith [mul_le_mul_of_nonneg_left hμ hs]
  have hXienv (s : ℝ) (hs : 0 ≤ s) :
      mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) s ≤
        theta M * mainEnvelopeXi vbar gammaZero mainSourceInversePrefix 1 s := by
    unfold mainEnvelopeXi
    nlinarith [mul_le_mul_of_nonneg_left hχ hs]
  refine ⟨hnode.1, fun s hs => ?_, ?_⟩
  · obtain ⟨h0, hle⟩ := hnode.2.1 s hs
    have hmean := main_envelope_a_actual_law_Th M h hM hγ N hpast m hm hs
    rw [← hbsq] at hmean
    have hfa : f s ≤ theta M * mainEnvelopeA vbar gammaZero mainSourceMeanPrefix s :=
      ((hle.trans (min_le_left _ _)).trans hmean).trans (hAenv s hs.1)
    have hfx : f s ≤ theta M * (mainEnvelopeXi vbar gammaZero mainSourceInversePrefix 1 s /
        mainBetaOld) := by
      have := (hle.trans (min_le_right _ _)).trans
        (div_le_div_of_nonneg_right (hXienv s hs.1) hbo.le)
      calc f s ≤ _ := this
        _ = _ := by ring
    refine ⟨div_nonneg h0 hθpos.le, le_min ?_ ?_⟩
    · rw [div_le_iff₀ hθpos]; linarith
    · rw [div_le_iff₀ hθpos]; linarith
  · filter_upwards [hnode.2.2.1] with s hs hs01
    have hd := hs hs01
    have hs0 := hs01.1
    have hmean := main_envelope_a_actual_law_Th M h hM hγ N hpast m hm hs01
    rw [← hbsq] at hmean
    have haθ : inSourceMeanActual M m 5 s ≤
        theta M * mainEnvelopeA vbar gammaZero mainSourceMeanPrefix s :=
      hmean.trans (hAenv s hs0)
    have hHθ : mainEnvelopeH35Theta (theta M) (b ^ 2) M.gamma s ≤
        theta M * mainEnvelopeH35 vbar gammaZero s := by
      rw [hθdef] at hb ⊢
      exact chrono_envH35Theta_scale_le hgpos hγ hs0 hvbar hb
    have hH0 : 0 ≤ mainEnvelopeH35Theta (theta M) (b ^ 2) M.gamma s := by
      unfold mainEnvelopeH35Theta; positivity
    have hE1 : mainSourceError' (b ^ 2) (inSourceMeanActual M m 5 s) (f s)
        (mainEnvelopeH35Theta (theta M) (b ^ 2) M.gamma s)
        (mainEnvelopeXi (b ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) s) q ≤
        mainSourceError' (theta M * vbar)
          (theta M * mainEnvelopeA vbar gammaZero mainSourceMeanPrefix s) (f s)
          (theta M * mainEnvelopeH35 vbar gammaZero s)
          (theta M * mainEnvelopeXi vbar gammaZero mainSourceInversePrefix 1 s) q :=
      chrono_sourceError_mono hq hv0 hb haθ hH0 hHθ (hXienv s hs0)
    have hfeq : f s = theta M * (f s / theta M) := by field_simp
    have hE2 := mainSourceError_theta_scale_le_Fq (theta := theta M) (v := vbar)
      (a := mainEnvelopeA vbar gammaZero mainSourceMeanPrefix s) (f := f s / theta M)
      (H := mainEnvelopeH35 vbar gammaZero s)
      (xi := mainEnvelopeXi vbar gammaZero mainSourceInversePrefix 1 s) (q := q)
      hθpos.le hθ1 hvbar (chrono_envH35_nonneg _ _ _) hq
    rw [← hfeq] at hE2
    have hI := th_inverseAbs_scale hθpos.le hθ1 hv0 hvbar hb hs0
    have hP1 : b ^ 2 * q ≤ theta M * vbar * q := mul_le_mul_of_nonneg_right hb hq
    have hP2 := th_affine_scale M hgpos hγ hq hs0 hb
    have hexp : theta M * (vbar * q + mainAffineTermGamma0 q s +
        mainSourceError' vbar (mainEnvelopeA vbar gammaZero mainSourceMeanPrefix s)
          (f s / theta M) (mainEnvelopeH35 vbar gammaZero s)
          (mainEnvelopeXi vbar gammaZero mainSourceInversePrefix 1 s) q +
        mainInverseAbs vbar (mainInverseMuMinusSource vbar) s) =
        theta M * vbar * q + theta M * mainAffineTermGamma0 q s +
        theta M * mainSourceError' vbar (mainEnvelopeA vbar gammaZero mainSourceMeanPrefix s)
          (f s / theta M) (mainEnvelopeH35 vbar gammaZero s)
          (mainEnvelopeXi vbar gammaZero mainSourceInversePrefix 1 s) q +
        theta M * mainInverseAbs vbar (mainInverseMuMinusSource vbar) s := by ring
    rw [hexp]
    linarith

end

end ASDExplicitGamma.Main
