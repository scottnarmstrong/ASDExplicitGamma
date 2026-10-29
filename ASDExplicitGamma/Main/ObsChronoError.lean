module

public import ASDExplicitGamma.Main.ObsChronoCoeff
public import ASDExplicitGamma.Main.ErrorProfile
public import ASDExplicitGamma.Main.InverseLowerAlgebra
public import ASDExplicitGamma.Main.HotGeneratorIntegrated

/-! STEP-MA-CHRONOLOGY-V-MONOTONE, part 2: the source error, its coefficients, the inverse term
and the affine term are nondecreasing in `v`, with monotone envelopes. -/

@[expose] public section

namespace ASDExplicitGamma.Main

noncomputable section

open Algsuperdiff.Section3 in
theorem chrono_mu_nonneg {gamma v : ℝ} (hg0 : 0 ≤ gamma) (hv : 0 ≤ v) : 0 ≤ mainMu v gamma := by
  have p0 := chrono_Pa_nonneg hv 0; have p1 := chrono_Pa_nonneg hv 1; have p2 := chrono_Pa_nonneg hv 2
  have hJ := chrono_J0_nonneg hg0 hv
  have hK := chrono_K0_nonneg hg0 hv
  have hKf := chrono_Kf_nonneg hv
  unfold mainMu mainBetaOld mainEpsOld
  positivity

theorem chrono_M0_mono {H H' : ℝ} (h : H ≤ H') : mainM0 H ≤ mainM0 H' := by
  unfold mainM0; gcongr

theorem chrono_M0_nonneg {H : ℝ} (hH : 0 ≤ H) : 0 ≤ mainM0 H := by
  unfold mainM0; positivity

theorem chrono_Tm_mono {H H' : ℝ} (hH : 0 ≤ H) (h : H ≤ H') : mainTm H ≤ mainTm H' := by
  have := chrono_M0_mono h
  have h0 := chrono_M0_nonneg hH
  have hD : 0 ≤ mainD := by unfold mainD mainAlpha; positivity
  have h0' : 0 ≤ mainM0 H' := chrono_M0_nonneg (hH.trans h)
  have hH' : 0 ≤ H' := hH.trans h
  have hDM : 0 ≤ mainD * mainM0 H' := mul_nonneg hD h0'
  unfold mainTm
  gcongr

theorem chrono_Bm_mono {H H' : ℝ} (h : H ≤ H') : mainBm H ≤ mainBm H' := by
  have := chrono_M0_mono h
  unfold mainBm mainBeta
  gcongr

theorem chrono_C_mono {H H' : ℝ} (h : H ≤ H') : mainC H ≤ mainC H' := by
  have := chrono_Bm_mono h
  unfold mainC; linarith

theorem chrono_T0_mono {x x' : ℝ} (h : x ≤ x') : mainT0 x ≤ mainT0 x' := by
  unfold mainT0; gcongr

theorem chrono_Be_mono {v w q : ℝ} (hq : 0 ≤ q) (hv : 0 ≤ v) (h : v ≤ w) :
    mainBe v q ≤ mainBe w q := by
  unfold mainBe; gcongr

theorem chrono_Be_nonneg {v q : ℝ} (hv : 0 ≤ v) : 0 ≤ mainBe v q := by
  unfold mainBe; positivity

theorem chrono_Ecov_mono {v w q : ℝ} (hq : 0 ≤ q) (hv : 0 ≤ v) (h : v ≤ w) :
    mainEcov v q ≤ mainEcov w q := by
  have h2 := chrono_mainA2_mono h
  have o := chrono_mainOp_mono hv h
  have o' := chrono_mainOm_mono hv h
  have h2n := chrono_mainA2_nonneg hv
  have on := chrono_mainOp_nonneg hv
  have on' := chrono_mainOm_nonneg hv
  have hw : 0 ≤ w := hv.trans h
  have onw := chrono_mainOp_nonneg hw
  have onw' := chrono_mainOm_nonneg hw
  have h2w := chrono_mainA2_nonneg hw
  unfold mainEcov
  gcongr

theorem chrono_LinearError_mono {v w H H' xi xi' q : ℝ} (hq : 0 ≤ q) (hv : 0 ≤ v) (h : v ≤ w)
    (hH : 0 ≤ H) (hHH : H ≤ H') (hxi : xi ≤ xi') :
    mainLinearError v H xi q ≤ mainLinearError w H' xi' q := by
  have o := chrono_mainOp_mono hv h
  have o' := chrono_mainOm_mono hv h
  have on := chrono_mainOp_nonneg hv
  have on' := chrono_mainOm_nonneg hv
  have kd := chrono_mainKd_mono hv h
  have kdn := chrono_mainKd_nonneg hv
  have tm := chrono_Tm_mono hH hHH
  have cm := chrono_C_mono hHH
  have m0 := chrono_M0_mono hHH
  have t0 := chrono_T0_mono hxi
  have hH' : 0 ≤ H' := hH.trans hHH
  have m0n := chrono_M0_nonneg hH
  have cn : 0 ≤ mainC H := by
    unfold mainC mainBm; positivity
  have hw : 0 ≤ w := hv.trans h
  have onw := chrono_mainOp_nonneg hw
  have onw' := chrono_mainOm_nonneg hw
  have kdw := chrono_mainKd_nonneg hw
  clear tm cm m0 t0 cn m0n
  unfold mainLinearError mainT0 mainTm mainC mainBm mainM0 mainBeta mainD mainAlpha
  have hH2 : 0 ≤ H := hH
  gcongr

theorem chrono_FourLoadAG_mono {v w H H' xi xi' q : ℝ} (hq : 0 ≤ q) (hv : 0 ≤ v) (h : v ≤ w)
    (hH : 0 ≤ H) (hHH : H ≤ H') (hxi : xi ≤ xi') :
    mainFourLoadAG v H xi q ≤ mainFourLoadAG w H' xi' q := by
  have o := chrono_mainOp_mono hv h
  have o' := chrono_mainOm_mono hv h
  have on := chrono_mainOp_nonneg hv
  have on' := chrono_mainOm_nonneg hv
  have kd := chrono_mainKd_mono hv h
  have kdn := chrono_mainKd_nonneg hv
  have be := chrono_Be_mono hq hv h
  have cm := chrono_C_mono hHH
  have t0 := chrono_T0_mono hxi
  have cn : 0 ≤ mainC H := by
    unfold mainC mainBm; positivity
  have hw : 0 ≤ w := hv.trans h
  have onw := chrono_mainOp_nonneg hw
  have onw' := chrono_mainOm_nonneg hw
  have kdw := chrono_mainKd_nonneg hw
  clear cm t0 cn
  unfold mainFourLoadAG mainT0 mainC mainBm mainM0 mainBeta
  gcongr

theorem chrono_error_mono {v w a a' f H H' xi xi' Lq Lq' ecov ecov' AG AG' be be' kd kd'
    krem krem' op op' om om' q : ℝ}
    (hv : 0 ≤ v) (hvw : v ≤ w) (ha : a ≤ a') (hH : 0 ≤ H) (hHH : H ≤ H') (hxi : xi ≤ xi')
    (hLq : Lq ≤ Lq') (he : 0 ≤ ecov) (hee : ecov ≤ ecov') (hAG : 0 ≤ AG) (hAGg : AG ≤ AG')
    (hbe : 0 ≤ be) (hbee : be ≤ be') (hkd : 0 ≤ kd) (hkdd : kd ≤ kd')
    (hkr : 0 ≤ krem) (hkrr : krem ≤ krem') (hop : 0 ≤ op) (hopp : op ≤ op')
    (hom : 0 ≤ om) (homm : om ≤ om') (hq : 0 ≤ q) :
    mainError' v a f H xi Lq ecov AG be kd krem op om q ≤
      mainError' w a' f H' xi' Lq' ecov' AG' be' kd' krem' op' om' q := by
  have hw : 0 ≤ w := hv.trans hvw
  have hH' : 0 ≤ H' := hH.trans hHH
  have he' : 0 ≤ ecov' := he.trans hee
  have hAG' : 0 ≤ AG' := hAG.trans hAGg
  have hbe' : 0 ≤ be' := hbe.trans hbee
  have hkd' : 0 ≤ kd' := hkd.trans hkdd
  have hkr' : 0 ≤ krem' := hkr.trans hkrr
  have hop' : 0 ≤ op' := hop.trans hopp
  have hom' : 0 ≤ om' := hom.trans homm
  have hKa := chrono_mainKa_mono hv hvw
  have hKan := chrono_mainKa_nonneg hv
  have hKaw := chrono_mainKa_nonneg hw
  unfold mainError' mainLoadZ mainLoadD mainLoadQ mainR1 mainR2 mainT0 mainV mainRec mainG
    mainHd mainM0 mainBeta mainEpsNew mainD mainAlpha mainBetaOld
  have h14 : 0 ≤ 1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (x := (3 : ℝ)) (z := -(1 / 4 : ℝ))
      (by norm_num) (by norm_num)
    linarith
  gcongr
  all_goals first | exact h14 | positivity

theorem chrono_sourceError_mono {v w a a' f H H' xi xi' q : ℝ}
    (hq : 0 ≤ q) (hv : 0 ≤ v) (hvw : v ≤ w) (ha : a ≤ a') (hH : 0 ≤ H) (hHH : H ≤ H')
    (hxi : xi ≤ xi') :
    mainSourceError' v a f H xi q ≤ mainSourceError' w a' f H' xi' q := by
  unfold mainSourceError'
  exact chrono_error_mono hv hvw ha hH hHH hxi
    (chrono_LinearError_mono hq hv hvw hH hHH hxi)
    (Real.sqrt_nonneg _) (chrono_Ecov_mono hq hv hvw)
    (by
      have hbe := chrono_Be_nonneg (q := q) hv
      have hkd := chrono_mainKd_nonneg hv
      have hop := chrono_mainOp_nonneg hv
      have hom := chrono_mainOm_nonneg hv
      unfold mainFourLoadAG mainC mainBm mainT0 mainBeta mainM0
      positivity) (chrono_FourLoadAG_mono hq hv hvw hH hHH hxi)
    (chrono_Be_nonneg hv) (chrono_Be_mono hq hv hvw)
    (chrono_mainKd_nonneg hv) (chrono_mainKd_mono hv hvw)
    (chrono_mainKrem_nonneg hv) (chrono_mainKrem_mono hv hvw)
    (chrono_mainOp_nonneg hv) (chrono_mainOp_mono hv hvw)
    (chrono_mainOm_nonneg hv) (chrono_mainOm_mono hv hvw) hq

theorem chrono_InvKA_mono {v w : ℝ} (hv : 0 ≤ v) (h : v ≤ w) :
    mainInverseKA v ≤ mainInverseKA w := by
  unfold mainInverseKA mainInverseA2 mainInverseA4
  gcongr

theorem chrono_InvKB_mono {v w : ℝ} (hv : 0 ≤ v) (h : v ≤ w) :
    mainInverseKB v ≤ mainInverseKB w := by
  unfold mainInverseKB mainInverseA2 mainInverseA4
  gcongr

theorem chrono_muMinus_mono {v w : ℝ} (hv : 0 ≤ v) (h : v ≤ w) :
    mainInverseMuMinusSource v ≤ mainInverseMuMinusSource w := by
  have a1 := chrono_InvKA_mono hv h
  have b1 := chrono_InvKB_mono hv h
  have a0 := mainInverseKA_nonneg v
  have b0 := mainInverseKB_nonneg v
  have a0w := mainInverseKA_nonneg w
  have b0w := mainInverseKB_nonneg w
  unfold mainInverseMuMinusSource mainInverseMuMinus
  gcongr

theorem chrono_kappa_mono {m m' : ℝ} (h : m ≤ m') : mainKappa m ≤ mainKappa m' := by
  unfold mainKappa mainBeta; gcongr

theorem chrono_inverseAbs_mono {v w t : ℝ} (hv : 0 ≤ v) (h : v ≤ w) (ht : 0 ≤ t) :
    mainInverseAbs v (mainInverseMuMinusSource v) t ≤
      mainInverseAbs w (mainInverseMuMinusSource w) t := by
  have hk := chrono_kappa_mono (chrono_muMinus_mono hv h)
  have hρ : 0 ≤ 2 + mainRho := by
    unfold mainRho mainEpsNew mainBeta; positivity
  have hexp : Real.exp (-(mainKappa (mainInverseMuMinusSource w) * t)) ≤
      Real.exp (-(mainKappa (mainInverseMuMinusSource v) * t)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hk ht])
  have h1 : 0 ≤ 1 - Real.exp (-(mainKappa (mainInverseMuMinusSource v) * t)) := by
    have : Real.exp (-(mainKappa (mainInverseMuMinusSource v) * t)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hmu : 0 ≤ mainKappa (mainInverseMuMinusSource v) := by
        unfold mainKappa mainBeta mainInverseMuMinusSource mainInverseMuMinus
        have := mainInverseKA_nonneg v; have := mainInverseKB_nonneg v; positivity
      nlinarith [mul_nonneg hmu ht]
    linarith
  unfold mainInverseAbs
  have hw : 0 ≤ w := hv.trans h
  calc v * (2 + mainRho) * (1 - Real.exp (-(mainKappa (mainInverseMuMinusSource v) * t)))
      ≤ w * (2 + mainRho) * (1 - Real.exp (-(mainKappa (mainInverseMuMinusSource v) * t))) := by
        gcongr
    _ ≤ w * (2 + mainRho) * (1 - Real.exp (-(mainKappa (mainInverseMuMinusSource w) * t))) := by
        have : 0 ≤ w * (2 + mainRho) := mul_nonneg hw hρ
        exact mul_le_mul_of_nonneg_left (by linarith) this

open Algsuperdiff.Section3 in
theorem chrono_affine_mono (M : ABKModel 2) {b b' q t : ℝ} (hg0 : 0 ≤ M.gamma)
    (hg : M.gamma ≤ gammaZero) (hq : 0 ≤ q) (ht : 0 ≤ t) (hb : b ^ 2 ≤ b' ^ 2) :
    mainAffineTerm M b q t ≤ mainAffineTerm M b' q t := by
  have hv : 0 ≤ b ^ 2 := sq_nonneg b
  have hA := chrono_envA_mono (a0 := mainSourceMeanPrefix) (t := t) hg0 hg hv hb ht
  have hpre : 0 ≤ mainSourceMeanPrefix := by
    have := mainSourceMeanPrefix_gate; linarith
  have hA0 : 0 ≤ mainEnvelopeA (b ^ 2) M.gamma mainSourceMeanPrefix t := by
    unfold mainEnvelopeA
    have : 0 ≤ mainMu (b ^ 2) M.gamma := chrono_mu_nonneg hg0 hv
    positivity
  have h2 := chrono_mainA2_mono hb
  have hβ : 0 ≤ mainBeta - 1 := by unfold mainBeta; norm_num
  unfold mainAffineTerm
  gcongr

end

end ASDExplicitGamma.Main
