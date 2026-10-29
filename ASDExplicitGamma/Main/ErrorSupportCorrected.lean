module

public import ASDExplicitGamma.Main.ErrorCorrected
public import ASDExplicitGamma.Main.ErrorSupport

/-! The support line of the corrected main error at an interior point. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set Filter
open scoped Topology

/-- The actual derivative and support line, with exactly the source
coefficient signs and strict interior-point gates. -/
theorem mainError_support (v a H xi Lq ecov AG be kd krem op om q anchor : ℝ)
    (hv : 0 < v) (hH : 0 ≤ H) (hecov : 0 ≤ ecov) (hbe : 0 ≤ be)
    (hkd : 0 ≤ kd) (hkrem : 0 ≤ krem) (ha : anchor < a) (hxi : mainBetaOld*anchor < xi) :
    let lambda := mainRadicalSlope (mainErrorSlope v)
      (mainErrorWeights' v H xi ecov be kd krem op om q) (mainErrorOffsets a H xi) mainErrorRates anchor
    0 < lambda ∧
      HasDerivAt (fun f => mainError' v a f H xi Lq ecov AG be kd krem op om q) (-lambda) anchor ∧
      ∀ f ∈ Icc 0 (min a (xi/mainBetaOld)),
        mainError' v a f H xi Lq ecov AG be kd krem op om q ≤
          mainError' v a anchor H xi Lq ecov AG be kd krem op om q + lambda*anchor-lambda*f := by
  intro lambda
  let weight := mainErrorWeights' v H xi ecov be kd krem op om q
  let offset := mainErrorOffsets a H xi
  let rate := mainErrorRates
  let c := mainErrorConstant v a H xi Lq AG kd op om q
  have hw := mainErrorWeights_nonneg v H xi ecov be kd krem op om q hecov hbe hkd hkrem
  have hanchor := mainError_anchor_radicands a H xi anchor hH ha hxi
  have heq : (fun f => mainError' v a f H xi Lq ecov AG be kd krem op om q) =ᶠ[𝓝 anchor]
      mainRadicalProfile c (mainErrorSlope v) weight offset rate := by
    have hi (i : Fin 3) : ∀ᶠ f in 𝓝 anchor, 0 < offset i-rate i*f :=
      (isOpen_lt continuous_const (by fun_prop : Continuous (fun f : ℝ => offset i-rate i*f))).mem_nhds (hanchor i)
    filter_upwards [Filter.eventually_all.2 hi] with f hf
    exact mainError_eq_radical v a f H xi Lq ecov AG be kd krem op om q (fun i => (hf i).le)
  refine ⟨mainRadicalSlope_pos _ _ _ _ _ (mainErrorSlope_pos hv) hw
    (fun i => (mainErrorRates_pos i).le), ?_, ?_⟩
  · exact (mainRadicalProfile_hasDerivAt c (mainErrorSlope v) weight offset rate anchor hanchor).congr_of_eventuallyEq heq
  · intro f hf
    have hh := mainRadicalProfile_support c (mainErrorSlope v) weight offset rate anchor f hw
      (mainError_interval_domain a H xi hH hf) hanchor
    rw [← mainError_eq_radical v a f H xi Lq ecov AG be kd krem op om q (mainError_interval_domain a H xi hH hf),
      ← mainError_eq_radical v a anchor H xi Lq ecov AG be kd krem op om q (fun i => (hanchor i).le)] at hh
    exact hh.trans_eq (by ring)

/-- The source support point is exactly 1/100. The two strict scalar gates
are explicit until the actual envelope/panel suppliers establish them. -/
theorem mainError_support_at_one_hundredth
    (v a H xi Lq ecov AG be kd krem op om q : ℝ)
    (hv : 0 < v) (hH : 0 ≤ H) (hecov : 0 ≤ ecov) (hbe : 0 ≤ be)
    (hkd : 0 ≤ kd) (hkrem : 0 ≤ krem)
    (ha : (1/100 : ℝ) < a) (hxi : mainBetaOld/100 < xi) :
    ∃ lambda : ℝ, 0 < lambda ∧
      lambda = -deriv (fun f => mainError' v a f H xi Lq ecov AG be kd krem op om q) (1/100) ∧
      ∀ f ∈ Icc 0 (min a (xi/mainBetaOld)),
        mainError' v a f H xi Lq ecov AG be kd krem op om q ≤
          mainError' v a (1/100) H xi Lq ecov AG be kd krem op om q + lambda/100-lambda*f := by
  have hxi' : mainBetaOld*(1/100 : ℝ) < xi := by simpa only [mul_one_div] using hxi
  obtain ⟨hlambda, hderiv, hsupport⟩ :=
    mainError_support v a H xi Lq ecov AG be kd krem op om q (1/100)
      hv hH hecov hbe hkd hkrem ha hxi'
  refine ⟨_, hlambda, ?_, ?_⟩
  · have hd := hderiv.deriv
    linarith only [hd]
  · intro f hf
    simpa only [mul_one_div] using hsupport f hf

end ASDExplicitGamma.Main
