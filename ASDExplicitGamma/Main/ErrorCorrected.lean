module

public import ASDExplicitGamma.Main.ErrorCoefficients
public import ASDExplicitGamma.Main.ErrorProfile

/-! The main error inventory: the covariance residual term carries
`√(v + v q / 4)` in place of `√v`. The original `mainError` is untouched. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set

noncomputable section

/-- Corrected full source additive error; `q` enters only through `√(v + v q/4)`. -/
def mainError' (v a f H xi Lq ecov AG be kd krem op om q : ℝ) : ℝ :=
  Lq + mainLoadZ v a f H xi kd ^ 2 +
  (v / 2 * mainR1 a f H ^ 2 +
    2 * (krem * mainR1 a f H + kd * mainT0 xi) * mainT0 xi * Real.sqrt (v + v * q / 4) +
    Real.sqrt 2 * mainT0 xi * mainR1 a f H * ecov) +
  2 * mainLoadD v a f H xi kd * mainLoadQ H op om + 2 * be * mainV xi f + AG * mainG xi +
  2 * kd * (63 / 50) *
    (Real.sqrt 2 * mainBeta * mainLoadD v a f H xi kd + mainLoadZ v a f H xi kd * mainRec xi)

/-- The literal source error with the covariance factor. -/
def mainSourceError' (v a f H xi q : ℝ) : ℝ :=
  mainError' v a f H xi (mainLinearError v H xi q) (mainEcov v q) (mainFourLoadAG v H xi q)
    (mainBe v q) (mainKd v) (mainKrem v) (mainOp v) (mainOm v) q

/-- Radical weights with `s = √(v + v q/4)` in the first entry. -/
def mainErrorWeights' (v H xi ecov be kd krem op om q : ℝ) : Fin 3 → ℝ :=
  ![2*krem*mainT0 xi*Real.sqrt (v + v*q/4) + Real.sqrt 2*mainT0 xi*ecov +
      2*mainKa v*mainLoadQ H op om + 2*kd*(63/50)*Real.sqrt 2*mainBeta*mainKa v,
    2*mainKa v*kd*mainErrorSourceRoot H xi + 2*kd*(63/50)*mainKa v*mainRec xi,
    2*be]

def mainErrorConstant (v a H xi Lq AG kd op om q : ℝ) : ℝ :=
  Lq+kd^2*(mainErrorSourceRoot H xi)^2 + 2*kd*(mainT0 xi)^2*Real.sqrt (v + v*q/4) +
    2*kd*mainT0 xi*mainLoadQ H op om + AG*mainG xi +
    2*kd*(63/50)*(Real.sqrt 2*mainBeta*kd*mainT0 xi +
      kd*mainErrorSourceRoot H xi*mainRec xi) +
    v/2*(mainErrorOffsets a H xi 0)+(mainKa v)^2*(mainErrorOffsets a H xi 1)

theorem mainError_polynomial_expansion
    (v a f H xi Lq ecov AG be kd krem op om q : ℝ) :
    mainError' v a f H xi Lq ecov AG be kd krem op om q =
      Lq+kd^2*(mainErrorSourceRoot H xi)^2+2*kd*(mainT0 xi)^2*Real.sqrt (v + v*q/4)+
      2*kd*mainT0 xi*mainLoadQ H op om+AG*mainG xi+
      2*kd*(63/50)*(Real.sqrt 2*mainBeta*kd*mainT0 xi+
        kd*mainErrorSourceRoot H xi*mainRec xi)+
      v/2*(mainR1 a f H)^2+(mainKa v)^2*(mainR2 a f H)^2+
      mainErrorWeights' v H xi ecov be kd krem op om q 0*mainR1 a f H+
      mainErrorWeights' v H xi ecov be kd krem op om q 1*mainR2 a f H+
      mainErrorWeights' v H xi ecov be kd krem op om q 2*mainV xi f := by
  simp only [mainError', mainLoadZ, mainLoadD, mainErrorSourceRoot, mainErrorWeights',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem mainError_eq_radical (v a f H xi Lq ecov AG be kd krem op om q : ℝ)
    (hf : f ∈ mainRadicalDomain (mainErrorOffsets a H xi) mainErrorRates) :
    mainError' v a f H xi Lq ecov AG be kd krem op om q =
      mainRadicalProfile (mainErrorConstant v a H xi Lq AG kd op om q) (mainErrorSlope v)
        (mainErrorWeights' v H xi ecov be kd krem op om q) (mainErrorOffsets a H xi)
        mainErrorRates f := by
  have heq (b e : ℝ) : b*a+e-b*f = b*(a-f)+e := by ring
  have h1 := hf 0
  have h2 := hf 1
  simp only [mainErrorOffsets, mainErrorRates, Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
  rw [heq] at h1 h2
  have hs1 := Real.sq_sqrt h1
  have hs2 := Real.sq_sqrt h2
  rw [mainError_polynomial_expansion]
  simp only [mainR1, mainR2, hs1, hs2]
  have hsum (g : Fin 3 → ℝ) : (∑ i, g i) = g 0+g 1+g 2 := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [mainRadicalProfile, hsum]
  simp only [mainErrorConstant, mainErrorSlope, mainErrorOffsets, mainErrorRates,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, heq, mainV]
  ring

theorem mainErrorWeights_nonneg (v H xi ecov be kd krem op om q : ℝ)
    (hecov : 0 ≤ ecov) (hbe : 0 ≤ be) (hkd : 0 ≤ kd) (hkrem : 0 ≤ krem) :
    ∀ i, 0 ≤ mainErrorWeights' v H xi ecov be kd krem op om q i := by
  have hka : 0 ≤ mainKa v := by unfold mainKa; positivity
  have ht : 0 ≤ mainT0 xi := Real.sqrt_nonneg _
  have hq : 0 ≤ mainLoadQ H op om := Real.sqrt_nonneg _
  have hsource : 0 ≤ mainErrorSourceRoot H xi := Real.sqrt_nonneg _
  have hrec : 0 ≤ mainRec xi := Real.sqrt_nonneg _
  have hb : 0 ≤ mainBeta := by norm_num [mainBeta]
  intro i
  fin_cases i <;> norm_num [mainErrorWeights'] <;> positivity

theorem mainError_concave (v a H xi Lq ecov AG be kd krem op om q : ℝ)
    (hH : 0 ≤ H) (hecov : 0 ≤ ecov) (hbe : 0 ≤ be) (hkd : 0 ≤ kd) (hkrem : 0 ≤ krem) :
    ConcaveOn ℝ (Icc 0 (min a (xi/mainBetaOld)))
      (fun f => mainError' v a f H xi Lq ecov AG be kd krem op om q) := by
  have h := mainRadicalProfile_concave (mainErrorConstant v a H xi Lq AG kd op om q)
    (mainErrorSlope v) (mainErrorWeights' v H xi ecov be kd krem op om q)
    (mainErrorOffsets a H xi) mainErrorRates
    (mainErrorWeights_nonneg v H xi ecov be kd krem op om q hecov hbe hkd hkrem)
  apply (h.subset (mainError_interval_domain a H xi hH) (convex_Icc _ _)).congr
  intro f hf
  exact (mainError_eq_radical v a f H xi Lq ecov AG be kd krem op om q
    (mainError_interval_domain a H xi hH hf)).symm

theorem mainError_antitone (v a H xi Lq ecov AG be kd krem op om q : ℝ)
    (hv : 0 ≤ v) (hH : 0 ≤ H) (hecov : 0 ≤ ecov) (hbe : 0 ≤ be) (hkd : 0 ≤ kd)
    (hkrem : 0 ≤ krem) :
    AntitoneOn (fun f => mainError' v a f H xi Lq ecov AG be kd krem op om q)
      (Icc 0 (min a (xi/mainBetaOld))) := by
  have hs : 0 ≤ mainErrorSlope v := by
    unfold mainErrorSlope
    exact add_nonneg (mul_nonneg (div_nonneg hv (by norm_num)) (by norm_num [mainBeta]))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have h := mainRadicalProfile_antitone (mainErrorConstant v a H xi Lq AG kd op om q)
    (mainErrorSlope v) (mainErrorWeights' v H xi ecov be kd krem op om q)
    (mainErrorOffsets a H xi) mainErrorRates hs
    (mainErrorWeights_nonneg v H xi ecov be kd krem op om q hecov hbe hkd hkrem)
    (fun i => (mainErrorRates_pos i).le)
  intro f hf g hg hfg
  change mainError' v a g H xi Lq ecov AG be kd krem op om q ≤
    mainError' v a f H xi Lq ecov AG be kd krem op om q
  rw [mainError_eq_radical v a f H xi Lq ecov AG be kd krem op om q
      (mainError_interval_domain a H xi hH hf),
    mainError_eq_radical v a g H xi Lq ecov AG be kd krem op om q
      (mainError_interval_domain a H xi hH hg)]
  exact h hfg

theorem mainSourceError_concave (v a H xi q : ℝ) (hv : 0 ≤ v) (hH : 0 ≤ H) :
    ConcaveOn ℝ (Set.Icc 0 (min a (xi/mainBetaOld)))
      (fun f => mainSourceError' v a f H xi q) :=
  mainError_concave _ _ _ _ _ _ _ _ _ _ _ _ _ hH (mainEcov_nonneg v q)
    (mainBe_nonneg hv q) (mainKd_nonneg v) (mainKrem_nonneg v)

theorem mainSourceError_antitone (v a H xi q : ℝ) (hv : 0 ≤ v) (hH : 0 ≤ H) :
    AntitoneOn (fun f => mainSourceError' v a f H xi q)
      (Set.Icc 0 (min a (xi/mainBetaOld))) :=
  mainError_antitone _ _ _ _ _ _ _ _ _ _ _ _ _ hv hH (mainEcov_nonneg v q)
    (mainBe_nonneg hv q) (mainKd_nonneg v) (mainKrem_nonneg v)

end
end ASDExplicitGamma.Main
