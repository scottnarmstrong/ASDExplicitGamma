module

public import ASDExplicitGamma.Scalar.FlatSourceQ3PositiveHaar
public import ASDExplicitGamma.Scalar.CutoffMeasurability
public import ASDExplicitGamma.Scalar.SmoothFeedbackGammaCovariance

/-! Measurability of the actual OLD-law affine directional Gamma matrix. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Main
open Algsuperdiff.Section3
open scoped BigOperators ENNReal

noncomputable section

private theorem gamma_hilbert_potential_coordinate_ae
    (Q : TriadicCube 2) (i : Fin 2)
    (X : HilbertBlockL2 (openCubeSet Q)) :
    hilbertVectorL2_normalizedCoordCLM Q i
        (hilbertBlockL2PotentialCLM X) =ᵐ[normalizedCubeMeasure Q]
      fun x => (hilbertBlockL2ToBlockL2 X x).1 i := by
  have hcoord := hilbertVectorL2_normalizedCoordCLM_ae Q i
    (hilbertBlockL2PotentialCLM X)
  have hraw : hilbertVectorL2ToVectorL2 (hilbertBlockL2PotentialCLM X) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => (hilbertBlockL2ToBlockL2 X x).1 := by
    filter_upwards [coeFn_hilbertVectorL2ToVectorL2
      (hilbertBlockL2PotentialCLM X), coeFn_hilbertBlockL2PotentialCLM X,
      coeFn_hilbertBlockL2ToBlockL2 X] with x hvec hpot hblock
    rw [hvec, hpot, hblock]
  have hdom : normalizedCubeMeasure Q ≤
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volumeMeasureOn (openCubeSet Q) := by
    rw [normalizedCubeMeasure_eq_smul_open Q]
  have habs : normalizedCubeMeasure Q ≪ volumeMeasureOn (openCubeSet Q) :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hraw' : hilbertVectorL2ToVectorL2 (hilbertBlockL2PotentialCLM X) =ᵐ[
      normalizedCubeMeasure Q]
      fun x => (hilbertBlockL2ToBlockL2 X x).1 := habs.ae_eq hraw
  exact hcoord.trans (hraw'.mono fun x hx => congrArg (fun z : Vec 2 => z i) hx)

private theorem gamma_hilbert_flux_coordinate_ae
    (Q : TriadicCube 2) (i : Fin 2)
    (X : HilbertBlockL2 (openCubeSet Q)) :
    hilbertVectorL2_normalizedCoordCLM Q i
        (hilbertBlockL2FluxCLM X) =ᵐ[normalizedCubeMeasure Q]
      fun x => (hilbertBlockL2ToBlockL2 X x).2 i := by
  have hcoord := hilbertVectorL2_normalizedCoordCLM_ae Q i
    (hilbertBlockL2FluxCLM X)
  have hraw : hilbertVectorL2ToVectorL2 (hilbertBlockL2FluxCLM X) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => (hilbertBlockL2ToBlockL2 X x).2 := by
    filter_upwards [coeFn_hilbertVectorL2ToVectorL2
      (hilbertBlockL2FluxCLM X), coeFn_hilbertBlockL2FluxCLM X,
      coeFn_hilbertBlockL2ToBlockL2 X] with x hvec hflux hblock
    rw [hvec, hflux, hblock]
  have hdom : normalizedCubeMeasure Q ≤
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volumeMeasureOn (openCubeSet Q) := by
    rw [normalizedCubeMeasure_eq_smul_open Q]
  have habs : normalizedCubeMeasure Q ≪ volumeMeasureOn (openCubeSet Q) :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hraw' : hilbertVectorL2ToVectorL2 (hilbertBlockL2FluxCLM X) =ᵐ[
      normalizedCubeMeasure Q]
      fun x => (hilbertBlockL2ToBlockL2 X x).2 := habs.ae_eq hraw
  exact hcoord.trans (hraw'.mono fun x hx => congrArg (fun z : Vec 2 => z i) hx)

private theorem gamma_normalized_ae_to_cube
    (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hfg : f =ᵐ[normalizedCubeMeasure Q] g) :
    f =ᵐ[cubeMeasure Q] g := by
  have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (cubeVolume_pos Q))
  have h' : f =ᵐ[ENNReal.ofReal ((cubeVolume Q)⁻¹) • cubeMeasure Q] g := by
    simpa [normalizedCubeMeasure] using hfg
  exact (Measure.ae_ennreal_smul_measure_iff hc).1 h'

private theorem gamma_primalEnergy_measurable_of_l2_map
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : TriadicCube 2)
    [MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [BorelSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    (q : ℝ) (hq : 0 ≤ q)
    (u : Ω → Lp ℝ 2 (normalizedCubeMeasure Q))
    (hu : Measurable u) :
    Measurable (fun ω => primalEnergy Q q (fun x => u ω x)) := by
  classical
  let a : ℕ → Ω → ℝ := fun n ω =>
    q ^ (n + 1) * ‖cubeIncrementL2CLM Q (n + 1) (u ω)‖ ^ 2
  let S : Ω → ℝ≥0∞ := fun ω => ∑' n, ENNReal.ofReal (a n ω)
  have ha (n : ℕ) : Measurable (a n) := by
    dsimp [a]
    have hn : Measurable (fun ω =>
        ‖cubeIncrementL2CLM Q (n + 1) (u ω)‖ ^ 2) :=
      (((cubeIncrementL2CLM Q (n + 1)).continuous.measurable.comp hu).norm.pow_const 2)
    simpa only [mul_comm] using hn.const_mul (q ^ (n + 1))
  have ha_nonneg (n : ℕ) (ω : Ω) : 0 ≤ a n ω := by
    dsimp [a]
    exact mul_nonneg (pow_nonneg hq _) (sq_nonneg _)
  have hS : Measurable S := by
    dsimp [S]
    exact Measurable.ennreal_tsum fun n => (ha n).ennreal_ofReal
  have htsum (ω : Ω) : (∑' n, a n ω) = (S ω).toReal := by
    by_cases htop : S ω = ∞
    · have hnot : ¬ Summable (fun n => a n ω) := by
        intro hs
        have hfinite := hs.tsum_ofReal_ne_top
        have hSfinite : S ω ≠ ∞ := by
          intro hInf
          exact hfinite (by simpa [S] using hInf)
        exact hSfinite htop
      rw [tsum_eq_zero_of_not_summable hnot, htop]
      rfl
    · let b : ℕ → NNReal := fun n => Real.toNNReal (a n ω)
      have hb (n : ℕ) : (b n : ℝ≥0∞) = ENNReal.ofReal (a n ω) := by
        simp [b, ENNReal.ofReal, Real.toNNReal_of_nonneg (ha_nonneg n ω)]
      have hsumB : Summable b := by
        apply (ENNReal.tsum_coe_ne_top_iff_summable).mp
        rw [show (∑' n, (b n : ℝ≥0∞)) = S ω from by
          apply tsum_congr
          intro n
          exact hb n]
        exact htop
      have hsumA : Summable (fun n => a n ω) := by
        have hsumReal : Summable (fun n => (b n : ℝ)) := NNReal.summable_coe.2 hsumB
        have hEq : (fun n => (b n : ℝ)) = fun n => a n ω := by
          funext n
          dsimp [b]
          exact Real.coe_toNNReal _ (ha_nonneg n ω)
        exact hEq ▸ hsumReal
      have hrepr : ENNReal.ofReal (∑' n, a n ω) = S ω := by
        dsimp [S]
        exact ENNReal.ofReal_tsum_of_nonneg (fun n => ha_nonneg n ω) hsumA
      have hsum_nonneg : 0 ≤ (∑' n, a n ω) := tsum_nonneg fun n => ha_nonneg n ω
      calc
        (∑' n, a n ω) = (ENNReal.ofReal (∑' n, a n ω)).toReal := by
          rw [ENNReal.toReal_ofReal hsum_nonneg]
        _ = (S ω).toReal := by rw [hrepr]
  have hbaseEq :
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x))) =
        fun ω => ‖cubeIncrementL2CLM Q 0 (u ω)‖ ^ 2 := by
    funext ω
    exact energy_cubeIncrement_eq_clm_norm_sq Q 0 (u ω)
  have hbase : Measurable
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x))) := by
    rw [hbaseEq]
    exact (((cubeIncrementL2CLM Q 0).continuous.measurable.comp hu).norm.pow_const 2)
  have hEq (ω : Ω) : primalEnergy Q q (fun x => u ω x) =
      energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal := by
    rw [primalEnergy]
    have hterm (n : ℕ) : q ^ (n + 1) * energy Q
        (cubeIncrement Q (n + 1) (fun x => u ω x)) = a n ω := by
      rw [energy_cubeIncrement_eq_clm_norm_sq]
    rw [tsum_congr hterm, htsum ω]
  have hresult : Measurable
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal) :=
    hbase.add hS.ennreal_toReal
  rw [show (fun ω => primalEnergy Q q (fun x => u ω x)) =
      fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal from by
        funext ω
        exact hEq ω]
  exact hresult

private theorem gamma_dualEnergy_measurable
    {Ω : Type*} [MeasurableSpace Ω] (Q : TriadicCube 2)
    [MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [BorelSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    (u : Ω → Lp ℝ 2 (normalizedCubeMeasure Q)) (hu : Measurable u) :
    Measurable (fun ω => dualEnergy Q (Real.sqrt 3) (fun x => u ω x)) := by
  unfold dualEnergy
  exact gamma_primalEnergy_measurable_of_l2_map Q (Real.sqrt 3)⁻¹
    (inv_nonneg.mpr (Real.sqrt_nonneg _)) u hu

theorem smooth_feedback_directional_gamma_measurable
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      smoothFeedbackCellDirectionalGamma M m Q e ω) := by
  classical
  let U := openCubeSet Q
  let μ := normalizedCubeMeasure Q
  let ν := M.nu
  let σ : ℝ := Annealed.sigmaBar M m
  let hν : 0 < ν := M.nu_pos
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let k : Cutoff.CutoffSample 2 → ResponseCoefficient U :=
    oldCutoffSkewCoefficient m Q
  let P : BlockVec 2 := (e, 0)
  let F : HilbertBlockL2 U := blockVecToHilbertBlockL2Const P
  let X : Cutoff.CutoffSample 2 → HilbertBlockL2 U := fun ω =>
    scalarProjectionResidual Q ν σ hν hσ (k ω) F
  let S : Cutoff.CutoffSample 2 → HilbertBlockL2 U := fun ω =>
    X ω + responseShearL2Operator σ hσ (k ω) (X ω)
  let uTop (i : Fin 2) (ω : Cutoff.CutoffSample 2) : Lp ℝ 2 μ :=
    hilbertVectorL2_normalizedCoordCLM Q i
      (hilbertBlockL2PotentialCLM (X ω)) - Lp.const 2 μ (e i)
  let uRecip (i : Fin 2) (ω : Cutoff.CutoffSample 2) : Lp ℝ 2 μ :=
    (σ / ν) • hilbertVectorL2_normalizedCoordCLM Q i
      (hilbertBlockL2FluxCLM (S ω))
  letI : MeasurableSpace (Lp ℝ 2 μ) := borel _
  letI : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  letI : OpensMeasurableSpace (Lp ℝ 2 μ) := ⟨le_of_eq rfl⟩
  letI : IsSeparable (volumeMeasureOn U) := inferInstance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 U) := inferInstance
  have hk : Measurable k := measurable_oldCutoffSkewCoefficient m Q
  have hX : Measurable X := by
    exact measurable_oldCutoff_scalarProjectionResidual m Q ν σ hν hσ F
  have hOp : Measurable (fun ω => responseShearL2Operator σ hσ (k ω)) :=
    (responseShearL2Family (measurableSet_openCubeSet Q) σ hσ).continuous.measurable.comp hk
  letI : OpensMeasurableSpace
      ((HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) × HilbertBlockL2 U) := inferInstance
  have hShear : Measurable (fun ω => responseShearL2Operator σ hσ (k ω) (X ω)) := by
    have hev : Continuous fun z :
        (HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) × HilbertBlockL2 U => z.1 z.2 := by
      fun_prop
    exact hev.measurable.comp (hOp.prodMk hX)
  have hS : Measurable S := hX.add hShear
  have hTopCLM (i : Fin 2) : Measurable (fun ω =>
      hilbertVectorL2_normalizedCoordCLM Q i
        (hilbertBlockL2PotentialCLM (X ω))) :=
    (hilbertVectorL2_normalizedCoordCLM Q i).continuous.measurable.comp
      ((hilbertBlockL2PotentialCLM (U := U)).continuous.measurable.comp hX)
  have hTop (i : Fin 2) : Measurable (uTop i) := by
    dsimp [uTop]
    exact (hTopCLM i).sub measurable_const
  have hFluxCLM : Measurable (fun ω => hilbertBlockL2FluxCLM (S ω)) :=
    (hilbertBlockL2FluxCLM (U := U)).continuous.measurable.comp hS
  have hRecipCLM (i : Fin 2) : Measurable (fun ω =>
      hilbertVectorL2_normalizedCoordCLM Q i
        (hilbertBlockL2FluxCLM (S ω))) :=
    (hilbertVectorL2_normalizedCoordCLM Q i).continuous.measurable.comp hFluxCLM
  have hRecip (i : Fin 2) : Measurable (uRecip i) := by
    dsimp [uRecip]
    exact (hRecipCLM i).const_smul (σ / ν)
  have hTopDual (i : Fin 2) : Measurable (fun ω =>
      dualEnergy Q (Real.sqrt 3) (fun x => uTop i ω x)) :=
    gamma_dualEnergy_measurable Q (uTop i) (hTop i)
  have hRecipDual (i : Fin 2) : Measurable (fun ω =>
      dualEnergy Q (Real.sqrt 3) (fun x => uRecip i ω x)) :=
    gamma_dualEnergy_measurable Q (uRecip i) (hRecip i)
  have hTopMem (i : Fin 2) (ω : Cutoff.CutoffSample 2) :
      MemLp (fun x => uTop i ω x) 2 μ := Lp.memLp (uTop i ω)
  have hRecipMem (i : Fin 2) (ω : Cutoff.CutoffSample 2) :
      MemLp (fun x => uRecip i ω x) 2 μ := Lp.memLp (uRecip i ω)
  have hResidualMem (ω : Cutoff.CutoffSample 2) : MemBlockL2 U
      (smoothFeedbackCellAffineResidual M m Q e ω) := by
    let a := responseFramePlanarCoefficientField ν σ (k ω)
    exact scalar_cell_response_test_memL2 Q a
      (responseFramePlanarCoefficientField_isElliptic
        (measurableSet_openCubeSet Q) ν σ hν hσ (k ω)) P
  have hTopActualMem (ω : Cutoff.CutoffSample 2) (i : Fin 2) :
      MemLp (fun x => smoothFeedbackCellAffineTopDefect M m Q e ω x i)
        2 μ := by
    have hfirst : MemBlockL2 U (smoothFeedbackCellAffineResidual M m Q e ω) :=
      hResidualMem ω
    exact memLp_normalized_of_memL2On
      ((memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hfirst) i).sub
        (memLp_const (e i)))
  have hEll (ω : Cutoff.CutoffSample 2) := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) ν σ hν hσ (k ω)
  have hFlux (ω : Cutoff.CutoffSample 2) : MemBlockL2 U
      (scalarCoefficientFlux (responseFramePlanarCoefficientField ν σ (k ω))
        (smoothFeedbackCellAffineResidual M m Q e ω)) :=
    scalar_coefficient_flux_memL2 Q _ (hEll ω) (hResidualMem ω)
  have hRecipActualMem (ω : Cutoff.CutoffSample 2) (i : Fin 2) :
      MemLp (fun x => smoothFeedbackCellAffineReciprocalGradient M m Q e ω x i)
        2 μ := by
    exact memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 (hFlux ω)) i)
  have hFconstant (ω : Cutoff.CutoffSample 2) :
      (scalarFrameRealization Q ν σ hν hσ (k ω)).constantField P = F := by
    change blockVecToHilbertBlockL2Const P = blockVecToHilbertBlockL2Const P
    rfl
  have hFconstant' (ω : Cutoff.CutoffSample 2) :
      (scalarFrameRealization Q ν σ hν hσ (k ω)).constantField (e, 0) = F := by
    simpa [P] using hFconstant ω
  have hResidualRep (ω : Cutoff.CutoffSample 2) : hilbertBlockL2ToBlockL2 (X ω) =ᵐ[
      volumeMeasureOn U] smoothFeedbackCellAffineResidual M m Q e ω := by
    have h := smooth_feedback_affine_projection_ae M m Q e ω
    simpa [scalarResidualField, X, k, F, U, ν, σ, hν, hσ, hFconstant' ω] using h
  have hTopCoord (ω : Cutoff.CutoffSample 2) : ∀ i : Fin 2,
      uTop i ω =ᵐ[μ] fun x =>
        smoothFeedbackCellAffineTopDefect M m Q e ω x i := by
    intro i
    change (hilbertVectorL2_normalizedCoordCLM Q i
        (hilbertBlockL2PotentialCLM (X ω)) - Lp.const 2 μ (e i)) =ᵐ[μ] _
    have hpot := gamma_hilbert_potential_coordinate_ae Q i (X ω)
    have hdom : μ ≤ ENNReal.ofReal ((cubeVolume Q)⁻¹) • volumeMeasureOn U := by
      change normalizedCubeMeasure Q ≤ _
      rw [normalizedCubeMeasure_eq_smul_open Q]
    have habs : μ ≪ volumeMeasureOn U := Measure.absolutelyContinuous_of_le_smul hdom
    have hrep := habs.ae_eq (hResidualRep ω)
    filter_upwards [Lp.coeFn_sub
        (hilbertVectorL2_normalizedCoordCLM Q i
          (hilbertBlockL2PotentialCLM (X ω))) (Lp.const 2 μ (e i)),
      Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := μ) (c := e i), hpot, hrep]
      with x hsub hconst hp hfield
    calc
      (hilbertVectorL2_normalizedCoordCLM Q i
          (hilbertBlockL2PotentialCLM (X ω)) -
            Lp.const 2 μ (e i) : Lp ℝ 2 μ) x =
          hilbertVectorL2_normalizedCoordCLM Q i
            (hilbertBlockL2PotentialCLM (X ω)) x -
              (Lp.const 2 μ (e i) : Lp ℝ 2 μ) x := hsub
      _ = smoothFeedbackCellAffineTopDefect M m Q e ω x i := by
        rw [hconst, hp, hfield]
        rfl
  have hRecipCoord (ω : Cutoff.CutoffSample 2) : ∀ i : Fin 2,
      uRecip i ω =ᵐ[μ] fun x =>
        smoothFeedbackCellAffineReciprocalGradient M m Q e ω x i := by
    intro i
    have hfluxCoord := gamma_hilbert_flux_coordinate_ae Q i (S ω)
    have hdom : μ ≤ ENNReal.ofReal ((cubeVolume Q)⁻¹) • volumeMeasureOn U := by
      change normalizedCubeMeasure Q ≤ _
      rw [normalizedCubeMeasure_eq_smul_open Q]
    have habs : μ ≪ volumeMeasureOn U := Measure.absolutelyContinuous_of_le_smul hdom
    have hshear := responseShearAffineL2_toBlockL2_ae σ hσ (k ω) (X ω)
    have hshear' : (fun x => (hilbertBlockL2ToBlockL2 (S ω) x).2) =ᵐ[μ]
        fun x => (responseShear σ (responseCoefficientExtension (k ω) x)
          (hilbertBlockL2ToBlockL2 (X ω) x)).2 := by
      exact habs.ae_eq (hshear.mono fun x hx => congrArg Prod.snd hx)
    have hflux := hfluxCoord.trans
      (hshear'.mono fun x hx => congrArg (fun z : Vec 2 => z i) hx)
    have hrep : hilbertBlockL2ToBlockL2 (X ω) =ᵐ[μ]
        smoothFeedbackCellAffineResidual M m Q e ω := habs.ae_eq (hResidualRep ω)
    have hshearRep : (fun x => (responseShear σ
        (responseCoefficientExtension (k ω) x)
        (hilbertBlockL2ToBlockL2 (X ω) x)).2 i) =ᵐ[μ]
        fun x => (responseShear σ (responseCoefficientExtension (k ω) x)
          (smoothFeedbackCellAffineResidual M m Q e ω x)).2 i :=
      hrep.mono fun x hx => congrArg
        (fun z : BlockVec 2 => (responseShear σ
          (responseCoefficientExtension (k ω) x) z).2 i) hx
    have hlower (x : Vec 2) :
        (blockMatVecMul
          (blockCoeffField (responseFramePlanarCoefficientField ν σ (k ω)) x)
          (smoothFeedbackCellAffineResidual M m Q e ω x)).2 =
          lemmaVConjugateGradient ν σ (responseCoefficientExtension (k ω) x)
            (smoothFeedbackCellAffineResidual M m Q e ω x) := by
      have h := lemmaV_planar_lower_image ν σ
        (responseCoefficientExtension (k ω) x) hν hσ
        (smoothFeedbackCellAffineResidual M m Q e ω x)
      simpa [responseFramePlanarCoefficientField, blockCoeffField] using h
    have hShearIdentity (x : Vec 2) :
        lemmaVConjugateGradient ν σ (responseCoefficientExtension (k ω) x)
          (smoothFeedbackCellAffineResidual M m Q e ω x) =
        (σ / ν) • (responseShear σ (responseCoefficientExtension (k ω) x)
          (smoothFeedbackCellAffineResidual M m Q e ω x)).2 := by
      ext j
      simp [lemmaVConjugateGradient, responseShear, responseShearCorrection,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
    have hscaled := hflux.trans hshearRep
    have hfinal : (σ / ν) •
        hilbertVectorL2_normalizedCoordCLM Q i
          (hilbertBlockL2FluxCLM (S ω)) =ᵐ[μ]
        fun x => smoothFeedbackCellAffineReciprocalGradient M m Q e ω x i := by
      filter_upwards [Lp.coeFn_smul (σ / ν)
          (hilbertVectorL2_normalizedCoordCLM Q i
            (hilbertBlockL2FluxCLM (S ω))), hscaled] with x hsmul hx
      dsimp [smoothFeedbackCellAffineReciprocalGradient,
        scalarCoefficientFlux, k, ν, σ]
      calc
        ((σ / ν) • hilbertVectorL2_normalizedCoordCLM Q i
            (hilbertBlockL2FluxCLM (S ω)) : Lp ℝ 2 μ) x =
            (σ / ν) * hilbertVectorL2_normalizedCoordCLM Q i
              (hilbertBlockL2FluxCLM (S ω)) x := by
          rw [hsmul]
          simp [Pi.smul_apply, smul_eq_mul]
        _ = (blockMatVecMul
            (blockCoeffField (responseFramePlanarCoefficientField ν σ (k ω)) x)
            (smoothFeedbackCellAffineResidual M m Q e ω x)).2 i := by
          calc
            (σ / ν) * hilbertVectorL2_normalizedCoordCLM Q i
                (hilbertBlockL2FluxCLM (S ω)) x =
                (σ / ν) •
                  (responseShear σ (responseCoefficientExtension (k ω) x)
                    (smoothFeedbackCellAffineResidual M m Q e ω x)).2 i := by
              rw [hx]
              simp [smul_eq_mul]
            _ = lemmaVConjugateGradient ν σ (responseCoefficientExtension (k ω) x)
                  (smoothFeedbackCellAffineResidual M m Q e ω x) i := by
              exact congrArg (fun z : Vec 2 => z i) (hShearIdentity x).symm
            _ = (blockMatVecMul
                  (blockCoeffField (responseFramePlanarCoefficientField ν σ (k ω)) x)
                  (smoothFeedbackCellAffineResidual M m Q e ω x)).2 i := by
              exact congrArg (fun z : Vec 2 => z i) (hlower x).symm
    simpa [uRecip] using hfinal
  have htopEnergy (ω : Cutoff.CutoffSample 2) :
      vectorWeakHaarEnergy Q
          (smoothFeedbackCellAffineTopDefect M m Q e ω) =
        ∑ i : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => uTop i ω x) := by
    unfold vectorWeakHaarEnergy
    apply Finset.sum_congr rfl
    intro i hi
    have hcube := gamma_normalized_ae_to_cube Q (hTopCoord ω i)
    have hcube' :
        (fun x => uTop i ω x) =ᵐ[volume.restrict (cubeSet Q)]
          fun x => smoothFeedbackCellAffineTopDefect M m Q e ω x i := by
      simpa [cubeMeasure] using hcube
    exact lemmaV_dualEnergy_congr_ae Q
      (by
        have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
          (by norm_num : (1 : ℝ) < 3)
        simpa using h)
      (hTopActualMem ω i) (hTopMem i ω) hcube'.symm
  have hrecipEnergy (ω : Cutoff.CutoffSample 2) :
      vectorWeakHaarEnergy Q
          (smoothFeedbackCellAffineReciprocalGradient M m Q e ω) =
        ∑ i : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => uRecip i ω x) := by
    unfold vectorWeakHaarEnergy
    apply Finset.sum_congr rfl
    intro i hi
    have hcube := gamma_normalized_ae_to_cube Q (hRecipCoord ω i)
    have hcube' :
        (fun x => uRecip i ω x) =ᵐ[volume.restrict (cubeSet Q)]
          fun x => smoothFeedbackCellAffineReciprocalGradient M m Q e ω x i := by
      simpa [cubeMeasure] using hcube
    exact lemmaV_dualEnergy_congr_ae Q
      (by
        have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
          (by norm_num : (1 : ℝ) < 3)
        simpa using h)
      (hRecipActualMem ω i) (hRecipMem i ω) hcube'.symm
  have hGammaEq (ω : Cutoff.CutoffSample 2) :
      smoothFeedbackCellDirectionalGamma M m Q e ω =
        (∑ i : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => uTop i ω x)) +
        ∑ i : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => uRecip i ω x) := by
    change vectorWeakHaarEnergy Q
        (smoothFeedbackCellAffineTopDefect M m Q e ω) +
      vectorWeakHaarEnergy Q
        (smoothFeedbackCellAffineReciprocalGradient M m Q e ω) = _
    rw [htopEnergy ω, hrecipEnergy ω]
  have hsum : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      (∑ i : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => uTop i ω x)) +
        ∑ i : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => uRecip i ω x)) := by
    apply (Finset.measurable_sum _ fun i hi => hTopDual i).add
    exact Finset.measurable_sum _ fun i hi => hRecipDual i
  rw [show (fun ω : Cutoff.CutoffSample 2 =>
      smoothFeedbackCellDirectionalGamma M m Q e ω) =
      fun ω => (∑ i : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => uTop i ω x)) +
        ∑ i : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => uRecip i ω x) from by
          funext ω
          exact hGammaEq ω]
  exact hsum

/-- Every entry of the actual polarization matrix is measurable under the
cutoff sample sigma algebra. -/
theorem smooth_feedback_gamma_matrix_entry_measurable
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (i j : Fin 2) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      smoothFeedbackCellGammaMatrix M m Q ω i j) := by
  have hsum := smooth_feedback_directional_gamma_measurable M m
    Q (basisVec i + basisVec j)
  have hi := smooth_feedback_directional_gamma_measurable M m
    Q (basisVec i)
  have hj := smooth_feedback_directional_gamma_measurable M m
    Q (basisVec j)
  simpa [smoothFeedbackCellGammaMatrix] using
    (hsum.sub hi).sub hj |>.div_const 2

end
end ASDExplicitGamma.Scalar
