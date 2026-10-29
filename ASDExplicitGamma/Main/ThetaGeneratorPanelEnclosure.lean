module

public import ASDExplicitGamma.Main.PanelLeafPrimitives
public import ASDExplicitGamma.Main.ObsNodes
public import ASDExplicitGamma.Main.ObsChronologyMonotone
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Main.ErrorSupportCorrected
public import ASDExplicitGamma.Main.InverseDeficitODE
public import ASDExplicitGamma.Numerics.MainReturnCertificate.RecurrenceFields
public import ASDExplicitGamma.Main.PanelComparison
public import ASDExplicitGamma.Main.PanelEndpointCertificate
public import ASDExplicitGamma.Main.PanelEnclosure

/-! MA-THETA-CONTINUATION: `panel_pointwise` / `panel_endpoint` for an arbitrary
function `u` (to be `f/θ`), generalised from `PanelEnclosure`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
  ASDExplicitGamma.Inverse ASDExplicitGamma Set
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open ASDExplicitGamma.Numerics ASDExplicitGamma.Numerics.Mirror
  ASDExplicitGamma.Numerics.MainReturnCertificate

noncomputable section

/-- The `ObsChronoV35` shape for an arbitrary function `u`. -/
def ThetaChronoShape (u : ℝ → ℝ) (hobs : ℕ) : Prop :=
  let q := mainAffineFlatBoundaryCapQ (hobs - 1)
  (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ u s ∧
      u s ≤ min (mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s)
        (mainEnvelopeXi panelVbar gammaZero mainSourceInversePrefix 1 s / mainBetaOld)) ∧
    (∀ᵐ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      deriv u s ≤ panelVbar * q +
        ((panelVbar / 2 * mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s +
          panelVbar * q * (mainBeta - 1) +
          (4 + 2 * Real.sqrt 2) * (156 / 5 : ℝ) * mainA2 panelVbar / 9) +
        mainSourceError' panelVbar (mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s)
          (u s) (mainEnvelopeH35 panelVbar gammaZero s)
          (mainEnvelopeXi panelVbar gammaZero mainSourceInversePrefix 1 s) q +
        mainInverseAbs panelVbar (mainInverseMuMinusSource panelVbar) s))

theorem panel_final_arith_Th {D C aff Ef Iabs Eanc lam f lamlow GU AU : ℝ}
    (hder : D ≤ C + (aff + Ef + Iabs)) (hsupf : Ef ≤ Eanc + lam * (1 / 100) - lam * f)
    (hgu : GU = C + (aff + (Eanc + 1 / 100 * lam) + Iabs)) (hgb : GU ≤ AU)
    (hlow : lamlow ≤ lam) (hf : 0 ≤ f) : D ≤ AU - lamlow * f := by
  nlinarith [mul_le_mul_of_nonneg_right hlow hf]

/-- Pointwise panel step: at one time `s` of the panel, the chronology bound and the certified leaf
bounds give the affine differential inequality. -/
theorem panel_pointwise_Th (hL : PanelLeafL1L2) (u : ℝ → ℝ) (hobs : ℕ)
    (d : MainPanelData) (e : PanelEndpoints) (hb : panelFormulaBounds d e)
    (hfields : panelRecurrenceFields e) (hanchor : d.anchor = 1 / 100)
    (hmean : (d.initialMean : ℝ) = mainSourceMeanPrefix)
    (hxi : (d.initialInverseMean : ℝ) = mainSourceInversePrefix + 1 / 10 ^ 12)
    (hq : (d.covarianceCap : ℝ) = mainAffineFlatBoundaryCapQ (hobs - 1))
    (s : ℝ) (hs0 : 0 ≤ s) (hsd : QInterval.Contains d.time s)
    (hdom : 0 ≤ u s ∧
      u s ≤
        min (mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s)
          (mainEnvelopeXi panelVbar gammaZero mainSourceInversePrefix 1 s / mainBetaOld))
    (hder : deriv (u) s ≤
      panelVbar * mainAffineFlatBoundaryCapQ (hobs - 1) +
        ((panelVbar / 2 * mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s +
          panelVbar * mainAffineFlatBoundaryCapQ (hobs - 1) * (mainBeta - 1) +
          (4 + 2 * Real.sqrt 2) * (156 / 5 : ℝ) * mainA2 panelVbar / 9) +
        mainSourceError' panelVbar (mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s)
          (u s) (mainEnvelopeH35 panelVbar gammaZero s)
          (mainEnvelopeXi panelVbar gammaZero mainSourceInversePrefix 1 s)
          (mainAffineFlatBoundaryCapQ (hobs - 1)) +
        mainInverseAbs panelVbar (mainInverseMuMinusSource panelVbar) s)) :
    deriv (u) s ≤
      (e.aUpper : ℝ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℝ) -
        (e.ellLower : ℝ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℝ) *
          u s := by
  classical
  obtain ⟨hf0, hfle⟩ := hdom
  have hvpos : 0 < panelVbar := mainSourceClock_pos (by norm_num [gammaZero])
  have hg0 : (0 : ℝ) ≤ gammaZero := by norm_num [gammaZero]
  obtain ⟨hAg, hXig⟩ := mainSourceEnvelope_support_gates (v := panelVbar) (gamma := gammaZero)
    (theta := 1) (t := s) hvpos.le hg0 le_rfl (by norm_num) hs0
  obtain ⟨hI, hmu, hchi⟩ := hL (mainPanelRealData d) s (1 / 100)
  have hAeq : mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s =
      (mainPanelRealData d).initialMean +
        evalReal (panelRealEnv (mainPanelRealData d) s (1 / 100)) pMeanSlope * s := by
    rw [hmu]
    simp only [mainEnvelopeA, mainPanelRealData, hmean]
    ring
  have hXieq : mainEnvelopeXi panelVbar gammaZero mainSourceInversePrefix 1 s =
      (mainPanelRealData d).initialInverseMean +
        evalReal (panelRealEnv (mainPanelRealData d) s (1 / 100)) pXiSlope * s := by
    rw [hchi]
    simp only [mainEnvelopeXi, mainPanelRealData, hxi]
    ring
  set A := mainEnvelopeA panelVbar gammaZero mainSourceMeanPrefix s with hAdef
  set Xi := mainEnvelopeXi panelVbar gammaZero mainSourceInversePrefix 1 s with hXidef
  set H := mainEnvelopeH35 panelVbar gammaZero s with hHdef
  set q := mainAffineFlatBoundaryCapQ (hobs - 1) with hqdef
  set f := u s with hfdef
  have hH0 : 0 ≤ H := by
    simp only [hHdef, mainEnvelopeH35]; exact sq_nonneg _
  have hq0 : 0 ≤ q := chrono_capQ_nonneg' (hobs - 1)
  have hsupp := mainError_support panelVbar A H Xi (mainLinearError panelVbar H Xi q)
    (mainEcov panelVbar q) (mainFourLoadAG panelVbar H Xi q) (mainBe panelVbar q)
    (mainKd panelVbar) (mainKrem panelVbar) (mainOp panelVbar) (mainOm panelVbar) q (1 / 100)
    hvpos hH0 (mainEcov_nonneg panelVbar q) (mainBe_nonneg hvpos.le q) (mainKd_nonneg panelVbar)
    (mainKrem_nonneg panelVbar) hAg (by linarith [hXig])
  obtain ⟨hlampos, -, hsup⟩ := hsupp
  have hfmem : f ∈ Icc 0 (min A (Xi / mainBetaOld)) := ⟨hf0, hfle⟩
  have hsupf := hsup f hfmem
  -- leaves at the reference point
  have hbpos : (0 : ℝ) < mainBeta := by norm_num [mainBeta]
  have hHd0 : 0 ≤ H / (1 - mainAlpha) := by
    have : 0 < 1 - mainAlpha := by
      have ha : mainAlpha < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      linarith
    positivity
  have hR1 : 0 < mainBeta * (A - 1 / 100) + mainEpsNew * (H / (1 - mainAlpha)) := by
    have : 0 ≤ mainEpsNew * (H / (1 - mainAlpha)) := by
      have : (0 : ℝ) ≤ mainEpsNew := by norm_num [mainEpsNew]
      positivity
    nlinarith
  have hR2 : 0 < mainBeta ^ 2 * (A - 1 / 100) +
      (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) * (H / (1 - mainAlpha)) := by
    have : 0 ≤ (2 * mainBeta * mainEpsNew + mainEpsNew ^ 2) * (H / (1 - mainAlpha)) := by
      have : (0 : ℝ) ≤ 2 * mainBeta * mainEpsNew + mainEpsNew ^ 2 := by
        norm_num [mainBeta, mainEpsNew]
      positivity
    nlinarith [sq_pos_of_pos hbpos]
  have hV : 0 < Xi - mainBetaOld * (1 / 100) := by
    have := hXig
    nlinarith
  have hlam := leaf_lambda (mainPanelRealData d) s (1 / 100)
    (by rw [← hAeq]; simpa using hR1) (by rw [← hAeq]; simpa using hR2)
    (by rw [← hXieq]; simpa using hV)
  have hen := leaf_energy (mainPanelRealData d) s (1 / 100)
    (by rw [← hAeq]; simpa using hR1.le)
  have hsl := leaf_support (mainPanelRealData d) s (1 / 100)
  have hgu := leaf_generatorUpper (mainPanelRealData d) s (1 / 100)
  rw [← hAeq, ← hXieq] at hlam hen
  have hb' := hb s hsd
  rw [hanchor] at hb'
  obtain ⟨-, hlamlow, -, -, hgb⟩ := hb'
  simp only [panelLambdaReal, panelGeneratorUpperReal, PanelEndpoints.lambdaLower,
    PanelEndpoints.generatorUpper] at hlamlow hgb
  push_cast at hlamlow hgb
  have hcap : (mainPanelRealData d).covarianceCap = q := hq
  rw [hcap, ← hHdef] at hlam hen
  rw [hcap, ← hAeq] at hgu
  have hInv : evalReal (panelRealEnv (mainPanelRealData d) s (1 / 100)) inverseAbsoluteExpr =
      mainInverseAbs panelVbar (mainInverseMuMinusSource panelVbar) s := hI
  have hlam' : evalReal (panelRealEnv (mainPanelRealData d) s (1 / 100)) negativeAnchorDerivativeExpr =
      mainRadicalSlope (mainErrorSlope panelVbar)
        (mainErrorWeights' panelVbar H Xi (mainEcov panelVbar q) (mainBe panelVbar q)
          (mainKd panelVbar) (mainKrem panelVbar) (mainOp panelVbar) (mainOm panelVbar) q)
        (mainErrorOffsets A H Xi) mainErrorRates (1 / 100) := hlam
  have hen' : evalReal (panelRealEnv (mainPanelRealData d) s (1 / 100)) energyExpr =
      mainError' panelVbar A (1 / 100) H Xi (mainLinearError panelVbar H Xi q)
        (mainEcov panelVbar q) (mainFourLoadAG panelVbar H Xi q) (mainBe panelVbar q)
        (mainKd panelVbar) (mainKrem panelVbar) (mainOp panelVbar) (mainOm panelVbar) q := hen
  have hlamlow' : (e.ellLower : ℝ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℝ) ≤
      evalReal (panelRealEnv (mainPanelRealData d) s (1 / 100)) negativeAnchorDerivativeExpr := by
    rcases hfields with ⟨-, hell, -, -, -, -⟩
    have hG : (0 : ℝ) < (ASDExplicitGamma.Numerics.Spike.gridScale : ℝ) := by
      norm_num [ASDExplicitGamma.Numerics.Spike.gridScale]
    exact (div_le_div_of_nonneg_right hell hG.le).trans hlamlow
  have hderE : deriv (u) s ≤
      panelVbar * q + (panelVbar / 2 * A + panelVbar * q * (mainBeta - 1) +
        (4 + 2 * Real.sqrt 2) * (156 / 5) * mainA2 panelVbar / 9 +
        mainError' panelVbar A f H Xi (mainLinearError panelVbar H Xi q) (mainEcov panelVbar q)
          (mainFourLoadAG panelVbar H Xi q) (mainBe panelVbar q) (mainKd panelVbar)
          (mainKrem panelVbar) (mainOp panelVbar) (mainOm panelVbar) q +
        mainInverseAbs panelVbar (mainInverseMuMinusSource panelVbar) s) := hder
  have hsupEq : evalReal (panelRealEnv (mainPanelRealData d) s (1 / 100)) supportLineExpr =
      mainError' panelVbar A (1 / 100) H Xi (mainLinearError panelVbar H Xi q)
        (mainEcov panelVbar q) (mainFourLoadAG panelVbar H Xi q) (mainBe panelVbar q)
        (mainKd panelVbar) (mainKrem panelVbar) (mainOp panelVbar) (mainOm panelVbar) q +
      1 / 100 * mainRadicalSlope (mainErrorSlope panelVbar)
        (mainErrorWeights' panelVbar H Xi (mainEcov panelVbar q) (mainBe panelVbar q)
          (mainKd panelVbar) (mainKrem panelVbar) (mainOp panelVbar) (mainOm panelVbar) q)
        (mainErrorOffsets A H Xi) mainErrorRates (1 / 100) := by
    rw [hsl, hen', hlam']
  rw [hsupEq, hInv] at hgu
  rw [hlam'] at hlamlow'
  exact panel_final_arith_Th hderE hsupf hgu hgb hlamlow' hf0

end

/-- One certified panel `[a, b] ⊆ [0,1]` of the actual observer trace: under the chronology node and
the L1/L2 leaves, the panel endpoint recurrence holds. -/
theorem panel_endpoint_Th (hL : PanelLeafL1L2) (u : ℝ → ℝ) (hobs : ℕ)
    (hChrono : ThetaChronoShape u hobs)
    (hAC : AbsolutelyContinuousOnInterval (u) 0 1)
    (d : MainPanelData) (e : PanelEndpoints) (hb : panelFormulaBounds d e)
    (hfields : panelRecurrenceFields e) (hanchor : d.anchor = 1 / 100)
    (hmean : (d.initialMean : ℝ) = mainSourceMeanPrefix)
    (hxi : (d.initialInverseMean : ℝ) = mainSourceInversePrefix + 1 / 10 ^ 12)
    (hq : (d.covarianceCap : ℝ) = mainAffineFlatBoundaryCapQ (hobs - 1))
    {a b : ℝ} (hab : a ≤ b) (hlen : b - a = (1 / 8 : ℝ)) (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hdsub : ∀ s ∈ Icc a b, QInterval.Contains d.time s) :
    u b ≤
      (e.rhoUpper : ℝ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℝ) *
          u a +
        (e.offsetUpper : ℝ) / (ASDExplicitGamma.Numerics.Spike.gridScale : ℝ) := by
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := fun s hs => ⟨ha0.trans hs.1, hs.2.trans hb1⟩
  obtain ⟨hdom, hae⟩ := hChrono
  refine main_panel_endpoint_bound e hab hlen (hAC.mono (by rw [Set.uIcc_of_le hab, Set.uIcc_of_le (zero_le_one' ℝ)]; exact hsub)) ?_
    (fun t ht => (hdom t (hsub ht)).1) hfields
  filter_upwards [hae] with t ht htab
  exact panel_pointwise_Th hL u hobs d e hb hfields hanchor hmean hxi hq t
    (ha0.trans htab.1) (hdsub t htab) (hdom t (hsub htab)) (ht (hsub htab))

end ASDExplicitGamma.Main
