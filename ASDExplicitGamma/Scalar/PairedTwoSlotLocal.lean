module

public import ASDExplicitGamma.Scalar.PairedTwoSlotHelpers

/-! Two-slot local paired Bessel inequality: a block field whose potential is a
gradient and whose flux is a solenoidal field plus a source `H`, forced in the
potential slot by `G`.  The potential mean is shifted by the `H` correction and the
flux-image mean by the `G` correction. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory
open ASDExplicitGamma.Scalar

noncomputable section

/-- Two-slot paired Bessel estimate. -/
theorem pairedBessel_forced_two_slot {Q : TriadicCube 2} {a : CoeffField 2}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2) (hWpot : IsBlockPotentialOn (openCubeSet Q) W)
    {H : Vec 2 → Vec 2} (hH : MemVectorL2 (openCubeSet Q) H)
    (hWsol : IsSolenoidalOn (openCubeSet Q) (fun x => W.flux x - H x))
    (hWmem : MemBlockL2 (openCubeSet Q) W.eval)
    (hWlower : MemVectorL2 (openCubeSet Q)
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2))
    {G : Vec 2 → Vec 2} (hG : MemVectorL2 (openCubeSet Q) G)
    (hforced : ∀ T : BlockState 2, ScalarVariation (openCubeSet Q) T.eval →
      volumeAverage (openCubeSet Q) (blockPairingIntegrand a T W) =
        volumeAverage (openCubeSet Q) (fun x => vecDot (T.potential x) (G x))) :
    vecDot (pairedPotentialMean (openCubeSet Q) W + pairedBesselSourceCorrectionVector hEll H)
        (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight⁻¹
          (pairedPotentialMean (openCubeSet Q) W + pairedBesselSourceCorrectionVector hEll H)) +
      vecDot (pairedFluxImageMean (openCubeSet Q) a W +
          pairedBesselSourceCorrectionVector hEll G)
        (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight⁻¹
          (pairedFluxImageMean (openCubeSet Q) a W +
            pairedBesselSourceCorrectionVector hEll G)) ≤
      blockPairingAverage (openCubeSet Q) a W W := by
  let U : Set (Vec 2) := openCubeSet Q
  let data := pairedBesselOpenCubeFamilyData hEll
  let F := data.family
  letI pairedBesselForcedFinite : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let D : Mat 2 := (coarseBlockMatrix U a).lowerRight
  let p := pairedPotentialMean U W + pairedBesselSourceCorrectionVector hEll H
  let g := pairedFluxImageMean U a W
  let t := pairedBesselSourceCorrectionVector hEll G
  let g' := g + t
  let e := matVecMul D⁻¹ g'
  let f := matVecMul D⁻¹ p
  let S : BlockState 2 := F.field (0, e)
  let R : BlockState 2 := pairedReflectState a (F.field (0, f))
  let T : BlockState 2 := S + R
  let q := vecDot p (matVecMul D⁻¹ p) + vecDot g' (matVecMul D⁻¹ g')
  have hvol : 0 < (MeasureTheory.volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  have hConv : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet Q
  obtain ⟨_, hCoarse, _, _, _, _, hDpos, _⟩ := exists_energyMap_coarseData hConv hEll hvol
  have hD : D.PosDef := by
    change (coarseBlockMatrix U a).lowerRight.PosDef
    rw [coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    exact hDpos
  have hdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hDe : matVecMul D e = g' := by
    dsimp [e]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hDf : matVecMul D f = p := by
    dsimp [f]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hFresp : ∀ P : BlockVec 2, BlockResponseSpace a U (F.field P) := data.response
  have hSmem : MemBlockL2 U S.eval := (F.admissible (0, e)).memBlockL2_eval
  have hSresp : BlockResponseSpace a U S := hFresp (0, e)
  have hSflux : MemVectorL2 U S.flux := by
    simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hSmem
  have hRresp : BlockResponseSpace a U R := by
    exact pairedReflectState_mem_responseSpace hConv hEll
      (hFresp (0, f)) (by
        simpa [BlockState.eval] using
          memVectorL2_snd_of_memBlockL2 (F.admissible (0, f)).memBlockL2_eval)
  have hRpot : MemVectorL2 U R.potential :=
    blockResponse_potential_memL2_of_mem_responseSpace hRresp
  have hRflux : MemVectorL2 U R.flux :=
    memVectorL2_upperImage hEll (hFresp (0, f)) (by
      simpa [BlockState.eval] using
        memVectorL2_snd_of_memBlockL2 (F.admissible (0, f)).memBlockL2_eval)
  have hRmem : MemBlockL2 U R.eval := by
    change MemBlockL2 U (fun x => (R.potential x, R.flux x))
    exact memBlockL2_blockField hRpot hRflux
  have hSpot : MemVectorL2 U S.potential := by
    simpa [BlockState.eval] using memVectorL2_fst_of_memBlockL2 hSmem
  have hTmem : MemBlockL2 U T.eval := by
    change MemBlockL2 U (fun x => (S.potential x + R.potential x,
      S.flux x + R.flux x))
    exact memBlockL2_blockField (hSpot.add hRpot) (hSflux.add hRflux)
  have hWW : IntegrableOn (blockPairingIntegrand a W W) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hWmem hEll
  have hWS : IntegrableOn (blockPairingIntegrand a W S) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hSmem hEll
  have hWR : IntegrableOn (blockPairingIntegrand a W R) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hRmem hEll
  have hSS : IntegrableOn (blockPairingIntegrand a S S) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hSmem hSmem hEll
  have hSR : IntegrableOn (blockPairingIntegrand a S R) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hSmem hRmem hEll
  have hRS : IntegrableOn (blockPairingIntegrand a R S) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hRmem hSmem hEll
  have hRR : IntegrableOn (blockPairingIntegrand a R R) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hRmem hRmem hEll
  have hST : IntegrableOn (blockPairingIntegrand a S T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hSmem hTmem hEll
  have hRT : IntegrableOn (blockPairingIntegrand a R T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hRmem hTmem hEll
  have hWT : IntegrableOn (blockPairingIntegrand a W T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hTmem hEll
  have hTT : IntegrableOn (blockPairingIntegrand a T T) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hTmem hTmem hEll
  have hmeanS : pairedPotentialMean U S = 0 :=
    pureBottom_potentialMean_eq_zero hvol.ne' F e
  have hcross : blockPairingAverage U a S R = 0 := by
    calc
      blockPairingAverage U a S R = vecDot f (pairedPotentialMean U S) :=
        reflectedBottom_represents_potentialMean hEll hConv F hFresp
          S hSresp.1 hSresp.2.1 hSmem f
      _ = 0 := by rw [hmeanS]; exact vecDot_zero_right _
  have hSgram : blockPairingAverage U a S S = vecDot e (matVecMul D e) := by
    have hbase := linearMuMinimizerFamily_pairing_eq_coarse F (0, e) (0, e)
    have hblock : blockVecDot (0, e) (blockMatVecMul (coarseBlockMatrix U a) (0, e)) =
        vecDot e (matVecMul D e) := by
      simp [blockVecDot, blockMatVecMul, D, matVecMul_zero, vecDot_zero_left]
    exact hbase.trans hblock
  have hRgram : blockPairingAverage U a R R = vecDot f (matVecMul D f) := by
    calc
      blockPairingAverage U a R R =
          blockPairingAverage U a (pairedReflectState a (F.field (0, f)))
            (pairedReflectState a (F.field (0, f))) := rfl
      _ = blockPairingAverage U a (F.field (0, f)) (F.field (0, f)) :=
        pairedReflect_pairingAverage_isometry hEll _ _
      _ = vecDot f (matVecMul D f) := by
        have hbase := linearMuMinimizerFamily_pairing_eq_coarse F (0, f) (0, f)
        have hblock : blockVecDot (0, f)
            (blockMatVecMul (coarseBlockMatrix U a) (0, f)) =
              vecDot f (matVecMul D f) := by
          simp [blockVecDot, blockMatVecMul, D, matVecMul_zero, vecDot_zero_left]
        exact hbase.trans hblock
  have hTgram : blockPairingAverage U a T T = q := by
    dsimp [T]
    rw [blockPairingAverage_add_left U a S R (S + R) hST hRT,
      blockPairingAverage_add_right U a S S R hSS hSR,
      blockPairingAverage_add_right U a R S R hRS hRR,
      hSgram, hRgram, hcross]
    rw [blockCoeff_pairingAverage_symmetric U a R S, hcross]
    simp only [zero_add, add_zero]
    calc
      vecDot e (matVecMul D e) + vecDot f (matVecMul D f) =
          vecDot e g' + vecDot f p := by rw [hDe, hDf]
      _ = vecDot g' (matVecMul D⁻¹ g') + vecDot p (matVecMul D⁻¹ p) := by
        change vecDot (matVecMul D⁻¹ g') g' + vecDot (matVecMul D⁻¹ p) p = _
        rw [vecDot_comm (matVecMul D⁻¹ g') g', vecDot_comm (matVecMul D⁻¹ p) p]
      _ = q := by dsimp [q]; ring
  have hWR' : blockPairingAverage U a W R = vecDot f p := by
    let Wc : BlockState 2 := { potential := W.potential, flux := fun x => W.flux x - H x }
    let H0 : BlockState 2 := { potential := fun _ => 0, flux := H }
    have hWpotL2 : MemVectorL2 U W.potential := by
      simpa [BlockState.eval] using memVectorL2_fst_of_memBlockL2 hWmem
    have hWfluxL2 : MemVectorL2 U W.flux := by
      simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hWmem
    have hWcmem : MemBlockL2 U Wc.eval := by
      change MemBlockL2 U (fun x => (W.potential x, W.flux x - H x))
      exact memBlockL2_blockField hWpotL2 (hWfluxL2.sub hH)
    have hH0mem : MemBlockL2 U H0.eval := by
      change MemBlockL2 U (fun x => ((0 : Vec 2), H x))
      exact memBlockL2_blockField (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := (0 : Vec 2))) hH
    have hsplit : W = Wc + H0 := by
      apply BlockState.ext
      · funext x
        change W.potential x = W.potential x + 0
        simp
      · funext x
        change W.flux x = (W.flux x - H x) + H x
        simp
    have hWcR : IntegrableOn (blockPairingIntegrand a Wc R) U :=
      blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hWcmem hRmem hEll
    have hH0R : IntegrableOn (blockPairingIntegrand a H0 R) U :=
      blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hH0mem hRmem hEll
    have h1 : blockPairingAverage U a Wc R = vecDot f (pairedPotentialMean U W) :=
      reflectedBottom_represents_potentialMean hEll hConv F hFresp Wc hWpot hWsol hWcmem f
    have h2 : blockPairingAverage U a H0 R =
        vecDot f (pairedBesselSourceCorrectionVector hEll H) :=
      fluxOnly_reflect_pairing hEll hH f
    calc
      blockPairingAverage U a W R = blockPairingAverage U a (Wc + H0) R := by rw [← hsplit]
      _ = blockPairingAverage U a Wc R + blockPairingAverage U a H0 R :=
        blockPairingAverage_add_left U a Wc H0 R hWcR hH0R
      _ = vecDot f p := by
        rw [h1, h2]; dsimp [p]; rw [vecDot_add_right]
  have hWpair : blockPairingAverage U a W T = q := by
    dsimp [T]
    rw [blockPairingAverage_add_right U a W S R hWS hWR,
      pairedBessel_forcedBottom_represents_fluxImageMean hEll F W hWmem hWlower
        hforced e,
      pairedBessel_sourcePairing_eq_dot hEll hG e, hWR']
    dsimp [q, e, f, g', g, t]
    calc
      _ = vecDot (matVecMul D⁻¹ (pairedFluxImageMean U a W +
            pairedBesselSourceCorrectionVector hEll G))
            (pairedFluxImageMean U a W + pairedBesselSourceCorrectionVector hEll G) +
          vecDot (matVecMul D⁻¹ p) p := by
        rw [← vecDot_add_right]
      _ = _ := by
        rw [vecDot_comm (matVecMul D⁻¹ (pairedFluxImageMean U a W +
              pairedBesselSourceCorrectionVector hEll G))
            (pairedFluxImageMean U a W + pairedBesselSourceCorrectionVector hEll G),
          vecDot_comm (matVecMul D⁻¹ p) p]
        ring
  have hCS := blockPairingAverage_sq_le_product hEll
    (measurableSet_of_isEllipticFieldOn hEll) W T hWW hWT hTT
  rw [hWpair, hTgram] at hCS
  have hDinv : D⁻¹.PosDef := hD.inv
  have hqnonneg : 0 ≤ q := by
    have hp : 0 ≤ vecDot p (matVecMul D⁻¹ p) := by
      by_cases hp0 : p = 0
      · simp [hp0, matVecMul_zero, vecDot_zero_left]
      · have hstrict := hDinv.dotProduct_mulVec_pos hp0
        exact le_of_lt (by simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hstrict)
    have hg : 0 ≤ vecDot g' (matVecMul D⁻¹ g') := by
      by_cases hg0 : g' = 0
      · simp [hg0, matVecMul_zero, vecDot_zero_left]
      · have hstrict := hDinv.dotProduct_mulVec_pos hg0
        exact le_of_lt (by simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hstrict)
    dsimp [q]
    exact add_nonneg hp hg
  have hEnergy : 0 ≤ blockEnergyAverage U a W := by
    unfold blockEnergyAverage
    apply volumeAverage_nonneg_of_nonneg_on (measurableSet_of_isEllipticFieldOn hEll)
    intro x hx
    unfold blockEnergyDensity
    have hp : 0 ≤ blockVecDot (W.eval x)
        (blockMatVecMul (blockCoeffField a x) (W.eval x)) := by
      simpa [blockCoeffField] using
        blockMatrixOfCoeff_quadratic_nonneg (hEll.2 x hx) (W.eval x)
    exact mul_nonneg (by norm_num) hp
  have hWWnonneg : 0 ≤ blockPairingAverage U a W W := by
    have hhalf := blockEnergyAverage_eq_half_blockPairingAverage_self U a W
    have hdouble : blockPairingAverage U a W W = 2 * blockEnergyAverage U a W := by
      rw [hhalf]
      ring
    rw [hdouble]
    positivity
  change q ≤ blockPairingAverage U a W W
  by_cases hq : q = 0
  · rw [hq]
    exact hWWnonneg
  · have hqpos : 0 < q := lt_of_le_of_ne hqnonneg (Ne.symm hq)
    by_contra hnot
    have hlt : blockPairingAverage U a W W < q := lt_of_not_ge hnot
    have hprod : 0 < q * (q - blockPairingAverage U a W W) :=
      mul_pos hqpos (sub_pos.mpr hlt)
    nlinarith [hCS]


end
end ASDExplicitGamma.Variational
