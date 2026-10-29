module

public import ASDExplicitGamma.Variational.PairedBessel

/-! Helper identities (public copies of private lemmas of `PairedBessel`). -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory
open ASDExplicitGamma.Scalar

noncomputable section

theorem blockCoeff_pairing_symmetric {d : ℕ} (a : CoeffField d)
    (X Y : BlockState d) (x : Vec d) :
    blockVecDot (X.eval x) (blockMatVecMul (blockCoeffField a x) (Y.eval x)) =
      blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x)) :=
  blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat
    (isSymmetricBlockMat_blockMatrixOfCoeff (a x)) (X.eval x) (Y.eval x)

theorem blockCoeff_pairingAverage_symmetric {d : ℕ} (U : Set (Vec d))
    (a : CoeffField d) (X Y : BlockState d) :
    blockPairingAverage U a X Y = blockPairingAverage U a Y X := by
  unfold blockPairingAverage blockPairingIntegrand volumeAverage
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  exact blockCoeff_pairing_symmetric a X Y x

theorem memVectorL2_upperImage {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {X : BlockState d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hX : BlockResponseSpace a U X) (hFlux : MemVectorL2 U X.flux) :
    MemVectorL2 U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) := by
  have hPot : MemVectorL2 U X.potential := blockResponse_potential_memL2_of_mem_responseSpace hX
  have hLower := blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
    hX hFlux hEll
  have hSymm := memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hPot
  have hSkew := memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hLower
  have hsum : MemVectorL2 U
      (fun x => matVecMul (symmPart (a x)) (X.potential x) +
        matVecMul (skewPart (a x))
          ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) := hSymm.add hSkew
  have hEq :
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) =
        (fun x => matVecMul (symmPart (a x)) (X.potential x) +
          matVecMul (skewPart (a x))
            ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) := by
    funext x
    change (blockMatVecMul (blockMatrixOfCoeff (a x))
        (X.potential x, X.flux x)).1 =
      matVecMul (symmPart (a x)) (X.potential x) +
        matVecMul (skewPart (a x))
          ((blockMatVecMul (blockMatrixOfCoeff (a x))
            (X.potential x, X.flux x)).2)
    rw [blockMatVecMul_blockMatrixOfCoeff_fst,
      blockMatVecMul_blockMatrixOfCoeff_snd]
  simpa [hEq] using hsum

theorem pairedReflectState_mem_responseSpace {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {X : BlockState d} {lam Lam : ℝ}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hConv : IsOpenBoundedConvexDomain U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hX : BlockResponseSpace a U X) (hFlux : MemVectorL2 U X.flux) :
    BlockResponseSpace a U (pairedReflectState a X) := by
  have hLower := blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
    hX hFlux hEll
  have hLowerPot : IsPotentialOn U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
    apply IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain hConv) hLower
    intro g hg hsol
    exact blockResponse_lowerImage_orthogonal_of_mem_responseSpace hX hsol
  have hUpperSol : IsSolenoidalOn U
      (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) :=
    blockResponse_upperImage_isSolenoidalOn_of_mem_responseSpace hX
  refine ⟨?_, ?_, ?_⟩
  · change IsPotentialOn U (pairedReflectState a X).potential
    simpa [pairedReflectState] using hLowerPot
  · change IsSolenoidalOn U (pairedReflectState a X).flux
    simpa [pairedReflectState] using hUpperSol
  · intro Y hY
    have hpoint : ∀ x ∈ U,
        blockVecDot (Y.eval x)
          (blockMatVecMul (blockCoeffField a x) ((pairedReflectState a X).eval x)) =
          vecDot (Y.potential x) (X.flux x) + vecDot (Y.flux x) (X.potential x) := by
      intro x hx
      rw [pairedReflectState_action hEll X hx]
      simp [BlockState.eval, blockVecDot, vecDot_comm, vecDot_zero_right]
    have hzero₁ : ∫ x in U, vecDot (Y.potential x) (X.flux x)
        ∂MeasureTheory.volume = 0 := by
      rcases hY.1 with ⟨φ, hφ⟩
      have hz := hX.2.1 φ
      simpa [hφ, vecDot_comm] using hz
    have hzero₂ : ∫ x in U, vecDot (Y.flux x) (X.potential x)
        ∂MeasureTheory.volume = 0 := by
      rcases hX.1 with ⟨φ, hφ⟩
      have hz := hY.2 φ
      simpa [hφ, vecDot_comm] using hz
    have hYpotL2 : MemVectorL2 U Y.potential := by
      rcases hY.1 with ⟨φ, hφ⟩
      simpa [hφ] using φ.grad_memVectorL2
    have hTerm1Int : MeasureTheory.IntegrableOn
        (fun x => vecDot (Y.potential x) (X.flux x)) U :=
      integrableOn_vecDot_of_memVectorL2 hYpotL2 hFlux
    have hrewrite :
        ∫ x in U, blockVecDot (Y.eval x)
          (blockMatVecMul (blockCoeffField a x)
            ((pairedReflectState a X).eval x)) ∂MeasureTheory.volume =
        ∫ x in U,
          (vecDot (Y.potential x) (X.flux x) +
            vecDot (Y.flux x) (X.potential x)) ∂MeasureTheory.volume := by
      apply setIntegral_congr_fun (measurableSet_of_isEllipticFieldOn hEll)
      intro x hx
      simpa only [Function.comp_apply] using hpoint x hx
    rw [hrewrite]
    by_cases hTerm2Int : MeasureTheory.IntegrableOn
        (fun x => vecDot (Y.flux x) (X.potential x)) U
    · rw [MeasureTheory.integral_add hTerm1Int hTerm2Int, hzero₁, hzero₂]
      simp
    · have hSumNotInt : ¬ MeasureTheory.IntegrableOn
          (fun x => vecDot (Y.potential x) (X.flux x) +
            vecDot (Y.flux x) (X.potential x)) U := by
        intro hSumInt
        exact hTerm2Int ((MeasureTheory.integrable_add_iff_integrable_right'
          (μ := MeasureTheory.volume.restrict U) hTerm1Int).mp hSumInt)
      rw [MeasureTheory.integral_undef hSumNotInt]

theorem admissibleCorrection_memBlockL2 {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {P : BlockVec d}
    {X : BlockState d} (hX : IsBlockMuAdmissible U P X) :
    MemBlockL2 U (fun x =>
      ((hX.toCorrectionFieldDataOfAdmissible).potential x,
        (hX.toCorrectionFieldDataOfAdmissible).flux x)) := by
  exact memBlockL2_blockField (hX.toCorrectionFieldDataOfAdmissible).potential_memL2
    (hX.toCorrectionFieldDataOfAdmissible).flux_memL2

/-- The first-component mean is represented by the reflected actual
pure-bottom minimizer. -/
theorem reflectedBottom_represents_potentialMean {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] {a : CoeffField d}
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hConv : IsOpenBoundedConvexDomain U)
    (F : LinearMuMinimizerFamily U a)
    (hFresp : ∀ P : BlockVec d, BlockResponseSpace a U (F.field P))
    (W : BlockState d) (hWpot : IsBlockPotentialOn U W)
    (hWsol : IsBlockSolenoidalOn U W)
    (hWmem : MemBlockL2 U W.eval) (e : Vec d) :
    blockPairingAverage U a W (pairedReflectState a (F.field (0, e))) =
      vecDot e (pairedPotentialMean U W) := by
  let S := F.field (0, e)
  let J := pairedReflectState a S
  let ha := F.admissible (0, e)
  have hSmem : MemBlockL2 U S.eval := ha.memBlockL2_eval
  have hSflux : MemVectorL2 U S.flux := by
    simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hSmem
  have hSresp : BlockResponseSpace a U S := hFresp (0, e)
  have hJresp := pairedReflectState_mem_responseSpace hConv hEll hSresp hSflux
  have hJpot : MemVectorL2 U J.potential :=
    blockResponse_potential_memL2_of_mem_responseSpace hJresp
  have hJflux : MemVectorL2 U J.flux := memVectorL2_upperImage hEll hSresp hSflux
  have hJmem : MemBlockL2 U J.eval := by
    change MemBlockL2 U (fun x => (J.potential x, J.flux x))
    exact memBlockL2_blockField hJpot hJflux
  have hInt : MeasureTheory.IntegrableOn (blockPairingIntegrand a W J) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hWmem hJmem hEll
  change IsPotentialOn U W.potential at hWpot
  rcases hWpot with ⟨w, hw⟩
  have hWpotMem : MemVectorL2 U W.potential := by
    rw [← hw]
    exact w.grad_memVectorL2
  have hcoordPot : ∀ i, MeasureTheory.IntegrableOn (fun x => W.potential x i) U := by
    intro i
    exact CorrectionFieldData.integrableOn_coord_of_memVectorL2
      hWpotMem i
  have hSpot : MemVectorL2 U S.potential := by
    simpa [BlockState.eval] using memVectorL2_fst_of_memBlockL2 hSmem
  have hfluxCorr : MemVectorL2 U (fun x => S.flux x - e) := ha.fluxCorrection_memL2
  have hprod₁ : MeasureTheory.IntegrableOn
      (fun x => vecDot (W.potential x) (S.flux x - e)) U :=
    integrableOn_vecDot_of_memVectorL2
      hWpotMem hfluxCorr
  have hprod₂ : MeasureTheory.IntegrableOn
      (fun x => vecDot (W.flux x) (S.potential x)) U :=
    integrableOn_vecDot_of_memVectorL2
      (by simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 hWmem) hSpot
  have hzero₁ : ∫ x in U, vecDot (W.potential x) (S.flux x - e)
      ∂MeasureTheory.volume = 0 := by
    have hz := ha.isSolenoidalZeroNormalTrace w
    simpa [hw, vecDot_comm] using hz
  have hzero₂ : ∫ x in U, vecDot (W.flux x) (S.potential x)
      ∂MeasureTheory.volume = 0 := by
    change IsSolenoidalOn U W.flux at hWsol
    rcases ha.isPotentialZeroTrace with ⟨u, hu⟩
    have hz := hWsol u
    simpa [hu] using hz
  have hzeroAvg₁ : volumeAverage U
      (fun x => vecDot (W.potential x) (S.flux x - e)) = 0 :=
    volumeAverage_eq_zero_of_integral_eq_zero hzero₁
  have hzeroAvg₂ : volumeAverage U
      (fun x => vecDot (W.flux x) (S.potential x)) = 0 :=
    volumeAverage_eq_zero_of_integral_eq_zero hzero₂
  have hconstInt : MeasureTheory.IntegrableOn
      (fun x => vecDot (W.potential x) e) U :=
    integrableOn_vecDot_of_memVectorL2
      hWpotMem
      (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := e))
  have hsumInt : MeasureTheory.IntegrableOn
      (fun x => vecDot (W.potential x) (S.flux x - e) +
        vecDot (W.potential x) e) U := hprod₁.add hconstInt
  have hsumPoint : (fun x => vecDot (W.potential x) (S.flux x)) =
      fun x => vecDot (W.potential x) (S.flux x - e) +
        vecDot (W.potential x) e := by
    funext x
    calc
      vecDot (W.potential x) (S.flux x) =
          vecDot (W.potential x) ((S.flux x - e) + e) := by
            congr 1
            exact (sub_add_cancel _ _).symm
      _ = vecDot (W.potential x) (S.flux x - e) +
          vecDot (W.potential x) e := vecDot_add_right _ _ _
  have hprodFirst : MeasureTheory.IntegrableOn
      (fun x => vecDot (W.potential x) (S.flux x)) U := by
    apply hsumInt.congr
    filter_upwards with x
    exact (congrFun hsumPoint x).symm
  have hmain : blockPairingAverage U a W J =
      volumeAverage U (fun x => vecDot (W.potential x) (S.flux x)) +
        volumeAverage U (fun x => vecDot (W.flux x) (S.potential x)) := by
    have hRaw : ∫ x in U, blockPairingIntegrand a W J x ∂MeasureTheory.volume =
        ∫ x in U, vecDot (W.potential x) (S.flux x) +
          vecDot (W.flux x) (S.potential x) ∂MeasureTheory.volume := by
      apply setIntegral_congr_fun (measurableSet_of_isEllipticFieldOn hEll)
      intro x hx
      change blockVecDot (W.eval x)
        (blockMatVecMul (blockCoeffField a x)
          ((pairedReflectState a S).eval x)) = _
      rw [pairedReflectState_action hEll S hx]
      simp [BlockState.eval, blockVecDot]
    calc
      blockPairingAverage U a W J = volumeAverage U
          (fun x => vecDot (W.potential x) (S.flux x) +
            vecDot (W.flux x) (S.potential x)) := by
        unfold blockPairingAverage volumeAverage
        rw [hRaw]
      _ = volumeAverage U (fun x => vecDot (W.potential x) (S.flux x)) +
          volumeAverage U (fun x => vecDot (W.flux x) (S.potential x)) :=
        volumeAverage_add hprodFirst hprod₂
  have hmeanSource : volumeAverage U
      (fun x => vecDot (W.potential x) (S.flux x)) = volumeAverage U
        (fun x => vecDot (W.potential x) (S.flux x - e) +
          vecDot (W.potential x) e) := by
    have hRaw : ∫ x in U, vecDot (W.potential x) (S.flux x) ∂MeasureTheory.volume =
        ∫ x in U, vecDot (W.potential x) (S.flux x - e) +
          vecDot (W.potential x) e ∂MeasureTheory.volume := by
      apply setIntegral_congr_fun (measurableSet_of_isEllipticFieldOn hEll)
      intro x hx
      exact congrFun hsumPoint x
    unfold volumeAverage
    rw [hRaw]
  rw [hmain, hzeroAvg₂, hmeanSource]
  change volumeAverage U
      ((fun x => vecDot (W.potential x) (S.flux x - e)) +
        (fun x => vecDot (W.potential x) e)) + 0 =
      vecDot e (pairedPotentialMean U W)
  rw [volumeAverage_add hprod₁ hconstInt, hzeroAvg₁]
  rw [volumeAverage_vecDot_right W.potential e hcoordPot]
  rw [vecDot_comm]
  simp only [zero_add, add_zero]
  change vecDot e (fun i => volumeAverage U (fun x => W.potential x i)) =
    vecDot e (volumeAverageVec U W.potential)
  apply congrArg (vecDot e)
  funext i
  rfl

/-- A forced compatible field has the same potential-mean Riesz identity as a
homogeneous field; the flux-image identity carries the exact load pairing
against the zero-trace minimizer potential. -/
theorem pairedBessel_forcedBottom_represents_fluxImageMean
    {U : Set (Vec 2)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField 2} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (F : LinearMuMinimizerFamily U a)
    (W : BlockState 2)
    (hWmem : MemBlockL2 U W.eval)
    (hWlower : MemVectorL2 U
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2))
    {G : Vec 2 → Vec 2}
    (hforced : ∀ T : BlockState 2, ScalarVariation U T.eval →
      volumeAverage U (blockPairingIntegrand a T W) =
        volumeAverage U (fun x => vecDot (T.potential x) (G x)))
    (e : Vec 2) :
    blockPairingAverage U a W (F.field (0, e)) =
      vecDot e (pairedFluxImageMean U a W) +
        volumeAverage U (fun x => vecDot (G x) ((F.field (0, e)).potential x)) := by
  let S := F.field (0, e)
  let C : BlockState 2 := { potential := fun _ => 0, flux := fun _ => e }
  let Adm := F.admissible (0, e)
  let Corr := Adm.toCorrectionFieldDataOfAdmissible
  let Y : BlockState 2 := { potential := Corr.potential, flux := Corr.flux }
  have hYmem : MemBlockL2 U Y.eval := by
    change MemBlockL2 U (fun x => (Y.potential x, Y.flux x))
    simpa [Y] using admissibleCorrection_memBlockL2 Adm
  have hYvar : ScalarVariation U Y.eval := by
    refine ⟨hYmem, ?_, ?_⟩
    · change IsPotentialZeroTraceOn U Corr.potential
      exact Adm.isPotentialZeroTrace
    · change IsSolenoidalZeroNormalTraceOn U Corr.flux
      exact Adm.isSolenoidalZeroNormalTrace
  have hCmem : MemBlockL2 U C.eval := by
    change MemBlockL2 U (blockField C.potential C.flux)
    exact memBlockL2_blockField
      (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := (0 : Vec 2)))
      (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := e))
  have hsplit : S = Y + C := by
    apply BlockState.ext
    · funext x
      change S.potential x = Y.potential x + C.potential x
      simp [S, Y, C, Corr, IsBlockMuAdmissible.toCorrectionFieldDataOfAdmissible]
    · funext x
      change S.flux x = S.flux x - e + e
      exact (sub_add_cancel _ _).symm
  have hYW : IntegrableOn (blockPairingIntegrand a Y W) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hYmem hWmem hEll
  have hCW : IntegrableOn (blockPairingIntegrand a C W) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hCmem hWmem hEll
  have hGsource := hforced Y hYvar
  have hsource : blockPairingAverage U a Y W =
      volumeAverage U (fun x => vecDot (G x) (S.potential x)) := by
    change volumeAverage U (blockPairingIntegrand a Y W) = _
    calc
      _ = volumeAverage U (fun x => vecDot (Y.potential x) (G x)) := hGsource
      _ = volumeAverage U (fun x => vecDot (G x) (S.potential x)) := by
        congr 1
        funext x
        rw [vecDot_comm]
        simp [S, Y, Corr, IsBlockMuAdmissible.toCorrectionFieldDataOfAdmissible]
  have hcoord : ∀ i, IntegrableOn
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2 i) U := by
    intro i
    exact CorrectionFieldData.integrableOn_coord_of_memVectorL2 hWlower i
  have hconst : blockPairingAverage U a C W =
      vecDot e (pairedFluxImageMean U a W) := by
    calc
      blockPairingAverage U a C W = volumeAverage U
          (fun x => vecDot e ((blockMatVecMul (blockCoeffField a x) (W.eval x)).2)) := by
        unfold blockPairingAverage
        congr 1
        funext x
        simp [C, blockPairingIntegrand, BlockState.eval, blockVecDot, blockCoeffField, vecDot]
      _ = vecDot e (pairedFluxImageMean U a W) :=
        volumeAverage_vecDot_left e
          (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2) hcoord
  calc
    blockPairingAverage U a W S = blockPairingAverage U a S W :=
      blockCoeff_pairingAverage_symmetric U a W S
    _ = blockPairingAverage U a (Y + C) W := by rw [← hsplit]
    _ = blockPairingAverage U a Y W + blockPairingAverage U a C W :=
      blockPairingAverage_add_left U a Y C W hYW hCW
    _ = _ := by rw [hsource, hconst]; ring

/-- Pairing of a flux-only block `(0,H)` with the reflected minimizer is the
source correction. -/
theorem fluxOnly_reflect_pairing {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) {H : Vec 2 → Vec 2}
    (hH : MemVectorL2 (openCubeSet Q) H) (f : Vec 2) :
    blockPairingAverage (openCubeSet Q) a
        ({ potential := fun _ => 0, flux := H } : BlockState 2)
        (pairedReflectState a ((pairedBesselOpenCubeFamilyData hEll).family.field (0, f))) =
      vecDot f (pairedBesselSourceCorrectionVector hEll H) := by
  rw [← pairedBessel_sourcePairing_eq_dot hEll hH f]
  unfold blockPairingAverage volumeAverage
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_of_isEllipticFieldOn hEll)]
    with x hx
  change blockVecDot (((0 : Vec 2), H x)) (blockMatVecMul (blockCoeffField a x)
    ((pairedReflectState a ((pairedBesselOpenCubeFamilyData hEll).family.field (0, f))).eval x)) = _
  rw [pairedReflectState_action hEll _ hx]
  simp [BlockState.eval, blockVecDot, vecDot_comm, vecDot_zero_right]

end
end ASDExplicitGamma.Variational
