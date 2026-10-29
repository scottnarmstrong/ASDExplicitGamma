module

public import ASDExplicitGamma.Inverse.RawShellPureFluxRows
public import ASDExplicitGamma.Native.VanishingBracketOverlap
public import ASDExplicitGamma.Variational.LemmaVTrace

/-! The actual centered q3 trace bracket row in the OLD response frame. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
noncomputable section

private theorem lemmaVH2Bn_le_rawTraceRemainderB
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) :
    lemmaVH2Bn ρ δ ≤ rawTraceRemainderB ρ δ := by
  have hA2 : lemmaVH2A2 = (23244 / 25 : ℝ) := by
    norm_num [lemmaVH2A2, lemmaVH2R1]
  have hc0 : (1 : ℝ) ≤ 1.860 := by norm_num
  have hc1 : (36 / 25 : ℝ) ≤ 2.36412 := by norm_num
  have hc2 : (57 / 200 : ℝ) ≤ 0.52288 := by norm_num
  have hp0 : 0 ≤ Real.sqrt (78 / 10 : ℝ) * ρ :=
    mul_nonneg (Real.sqrt_nonneg _) hρ
  have hp1 : 0 ≤ Real.sqrt (78 / 5 : ℝ) * δ :=
    mul_nonneg (Real.sqrt_nonneg _) hδ
  have hp2 : 0 ≤ Real.sqrt (23244 / 25 : ℝ) * δ ^ 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)
  unfold lemmaVH2Bn rawTraceRemainderB lemmaVH2R1 lemmaVH2C1 lemmaVH2C2
  rw [hA2]
  rw [show (78 / 5 : ℝ) / 2 = 78 / 10 by norm_num]
  change (Real.sqrt (78 / 10 : ℝ) * ρ +
      (36 / 25 : ℝ) * Real.sqrt (78 / 5 : ℝ) * δ +
      (57 / 200 : ℝ) * Real.sqrt (23244 / 25 : ℝ) * δ ^ 2) ≤
    1.860 * Real.sqrt (78 / 10 : ℝ) * ρ +
      2.36412 * Real.sqrt (78 / 5 : ℝ) * δ +
      0.52288 * Real.sqrt (23244 / 25 : ℝ) * δ ^ 2
  have h0 := mul_le_mul_of_nonneg_right hc0 hp0
  have h1 := mul_le_mul_of_nonneg_right hc1 hp1
  have h2 := mul_le_mul_of_nonneg_right hc2 hp2
  nlinarith only [h0, h1, h2]

/-- The first derivative of the actual closed-cube trace is the derivative of
the open response trace along the exact restriction map. -/
theorem raw_trace_model_fderiv_openRestriction
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x d : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    fderiv ℝ (modelTraceObservable n ν σ) x d =
      fderiv ℝ (lemmaVTrace n ν σ) (pureFluxOpenResponseRestriction n x)
        (pureFluxOpenResponseRestriction n d) := by
  let R := pureFluxOpenResponseRestriction n
  have htrace : modelTraceObservable n ν σ = fun y =>
      lemmaVTrace n ν σ (R y) := by
    funext y
    exact modelTraceObservable_eq_lemmaVTrace_openRestriction n ν σ hν hσ y
  have henergy (p : Fin 2 × Bool) : DifferentiableAt ℝ
      (lemmaVLoadEnergy n ν σ hν hσ p) (R x) :=
    ((responseFrameEnergyObservable_contDiff (measurableSet_openCubeSet
      (originCube 2 n)) (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
      ν σ hν hσ (orthonormalFrameLoad p.1 (lemmaVLoadSign p.2))).differentiable
        (by norm_num)).differentiableAt
  have hsum : DifferentiableAt ℝ
      (fun z => ∑ p : Fin 2 × Bool, lemmaVLoadEnergy n ν σ hν hσ p z) (R x) := by
    apply DifferentiableAt.fun_sum
    intro p hp
    exact henergy p
  have hV : DifferentiableAt ℝ (lemmaVTrace n ν σ) (R x) := by
    have hEq : lemmaVTrace n ν σ = fun z =>
        (∑ p : Fin 2 × Bool, lemmaVLoadEnergy n ν σ hν hσ p z) - 4 := by
      funext z
      exact lemmaVTrace_eq_load_sum n ν σ hν hσ z
    rw [hEq]
    exact hsum.sub_const 4
  have hcomp := (hV.hasFDerivAt.comp x R.hasFDerivAt).fderiv
  rw [htrace]
  change fderiv ℝ (lemmaVTrace n ν σ ∘ ⇑R) x d = _
  rw [hcomp]
  rfl

/-- The response-coefficient q3 direction used by Lemma V is sigma times the
restriction of the actual centered heat direction. -/
theorem raw_trace_q3_native_response_eq_centered
    (n : ℤ) (σ b : ℝ) (L : {l : ℝ // 0 < l}) (j : ℕ) :
    mainCubeQ3ResponseDirection n σ b L (mainCubeRectangleCenter n)
        (mainCubeQ3WhiteNoiseSequence j) =
      σ • pureFluxMainCubeQ3CenteredResponseCoefficient n b L j := by
  classical
  let Q := originCube 2 n
  let center := pureFluxParentCenter n
  let H := pureFluxMainCubeQ3Directions n b L j
  have hcenter : (mainCubeRectangleCenter n).1 = center.1 := rfl
  have hmap : centeringMap center H = pureFluxCoefficientCentering center H := by
    ext y
    simp [centeringMap, pureFluxCoefficientCentering]
  have hfield :
      mainCubeResponseAdapter n
        (mainCubeQ3PhysicalField n b L (mainCubeRectangleCenter n)
          (mainCubeQ3WhiteNoiseSequence j)) =
        pureFluxOpenResponseRestriction n (centeringMap center H) := by
    ext y
    simp [mainCubeResponseAdapter, pureFluxOpenResponseRestriction,
      pureFluxOpenClosureInclusion, ContinuousMap.compCLM_apply,
      BoundedContinuousFunction.compContinuousCLM_apply,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply,
      mainCubeQ3PhysicalField, H, pureFluxMainCubeQ3Directions,
      mainCubeQ3WhiteNoiseSequence, centeringMap, hcenter,
      mainCubeH3Value_direction, mainQ3GlobalDirection, center,
      pureFluxParentCenter]
  rw [mainCubeQ3ResponseDirection, hfield, hmap,
    pureFluxMainCubeQ3CenteredResponseCoefficient_eq_restriction]

/-- The actual q3 remainder contribution to the OLD trace bracket with the
sharp SHEAR (3.2) coefficient `lemmaVH2Bn`, before its historical outward
rounding. -/
theorem raw_trace_model_q3_remainder_bracket_row_tight
    (n : ℤ) (s : ℕ) (ν σ b : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let L := q3ModelLength (n + (s : ℤ))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let R := fun j => centeringMap center (H j)
    let k := pureFluxOpenResponseRestriction n x
    let B := lemmaVTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ k)
    let ρ := cubeScaleFactor Q / L.1
    let δ := diagMeshRadius Q (pureFluxBankSourceDepth s) / L.1
    let v := b ^ 2 / σ ^ 2
    Summable (fun j =>
      (fderiv ℝ (modelTraceObservable n ν σ) x (R j)) ^ 2) ∧
    (∑' j, (fderiv ℝ (modelTraceObservable n ν σ) x (R j)) ^ 2) ≤
      4 * v * (lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
        (modelTraceObservable n ν σ x) * (modelTraceObservable n ν σ x + 4) := by
  classical
  intro Q L center H R k B ρ δ v
  let dModel : ℕ → ℝ :=
    fun j => fderiv ℝ (modelTraceObservable n ν σ) x (R j)
  let dNative : ℕ → ℝ := fun j =>
    fderiv ℝ (lemmaVTrace n ν σ) k
      (mainCubeQ3ResponseDirection n σ b L (mainCubeRectangleCenter n)
        (mainCubeQ3WhiteNoiseSequence j))
  have hbr := mainCubeQ3TraceRemainderBracket n
    (pureFluxBankSourceDepth s) ν σ b hν hσ L k
  have hdir (j : ℕ) :
      mainCubeQ3ResponseDirection n σ b L (mainCubeRectangleCenter n)
        (mainCubeQ3WhiteNoiseSequence j) =
      σ • pureFluxMainCubeQ3CenteredResponseCoefficient n b L j :=
    raw_trace_q3_native_response_eq_centered n σ b L j
  have hcentered (j : ℕ) :
      pureFluxMainCubeQ3CenteredResponseCoefficient n b L j =
        pureFluxOpenResponseRestriction n (R j) := by
    rw [pureFluxMainCubeQ3CenteredResponseCoefficient_eq_restriction]
    congr 1
    ext y
    simp [R, H, center, pureFluxCoefficientCentering, centeringMap]
  have hderiv (j : ℕ) : dNative j = σ * dModel j := by
    dsimp [dNative, dModel]
    rw [hdir j]
    simp only [map_smul, smul_eq_mul]
    rw [hcentered j,
      raw_trace_model_fderiv_openRestriction n ν σ hν hσ x (R j)]
  have hsum : Summable (fun j => (dModel j) ^ 2) := by
    have hscaled : Summable (fun j => (σ ^ 2)⁻¹ * (dNative j) ^ 2) := by
      simpa [dNative] using hbr.2.1.mul_left (σ ^ 2)⁻¹
    apply hscaled.congr
    intro j
    rw [hderiv j]
    field_simp [hσ.ne']
  have hsumEq : (∑' j, (dNative j) ^ 2) =
      σ ^ 2 * ∑' j, (dModel j) ^ 2 := by
    calc
      _ = ∑' j, σ ^ 2 * (dModel j) ^ 2 := by
        apply tsum_congr
        intro j
        rw [hderiv j]
        ring
      _ = _ := tsum_mul_left
  have htrace : lemmaVTrace n ν σ k = modelTraceObservable n ν σ x := by
    simpa [k] using
      (modelTraceObservable_eq_lemmaVTrace_openRestriction n ν σ hν hσ x).symm
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    exact div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le L.2.le
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact div_nonneg (diagMeshRadius_pos Q (pureFluxBankSourceDepth s)).le L.2.le
  have hBn : 0 ≤ lemmaVH2Bn ρ δ := by
    unfold lemmaVH2Bn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2 lemmaVH2A2
    positivity
  have hnative0 := hbr.2.2
  change (∑' j, (dNative j) ^ 2) ≤
    4 * (Real.sqrt (b ^ 2) * lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
      lemmaVTrace n ν σ k * (lemmaVTrace n ν σ k + 4) at hnative0
  rw [hsumEq, htrace] at hnative0
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
  have hnativeComm : (∑' j, (dModel j) ^ 2) * σ ^ 2 ≤
      4 * (Real.sqrt (b ^ 2) * lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
        modelTraceObservable n ν σ x * (modelTraceObservable n ν σ x + 4) := by
    simpa only [mul_comm] using hnative0
  have hnative : (∑' j, (dModel j) ^ 2) ≤
      (4 * (Real.sqrt (b ^ 2) * lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
        modelTraceObservable n ν σ x * (modelTraceObservable n ν σ x + 4)) /
        σ ^ 2 := (le_div_iff₀ hσ2).2 hnativeComm
  have hcoeff : (Real.sqrt (b ^ 2) * lemmaVH2Bn ρ δ) ^ 2 / σ ^ 2 =
      (b ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (sq_nonneg b)]
    ring
  have hT0 : 0 ≤ modelTraceObservable n ν σ x :=
    modelTraceObservable_nonneg n ν σ hν hσ x
  have hB0 : 0 ≤ B := lemmaVTileHistory_nonneg Q
    (pureFluxBankSourceDepth s)
    (responseFramePlanarCoefficientField ν σ k)
  have hC : 0 ≤ 4 * B ^ 2 * modelTraceObservable n ν σ x *
      (modelTraceObservable n ν σ x + 4) := by positivity
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ (4 * (Real.sqrt (b ^ 2) * lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
        modelTraceObservable n ν σ x * (modelTraceObservable n ν σ x + 4)) /
        σ ^ 2 := hnative
    _ = (4 * B ^ 2 * modelTraceObservable n ν σ x *
        (modelTraceObservable n ν σ x + 4)) *
        ((Real.sqrt (b ^ 2) * lemmaVH2Bn ρ δ) ^ 2 / σ ^ 2) := by ring
    _ = 4 * v * (lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
        modelTraceObservable n ν σ x * (modelTraceObservable n ν σ x + 4) := by
      rw [hcoeff]
      dsimp [v]
      field_simp [hσ.ne']

/-- The historical outward `B(ρ,δ)` form retained for consumers that use the
SHEAR decimal envelope rather than the 340 coefficient certificate. -/
theorem raw_trace_model_q3_remainder_bracket_row
    (n : ℤ) (s : ℕ) (ν σ b : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let Q := originCube 2 n
    let L := q3ModelLength (n + (s : ℤ))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let R := fun j => centeringMap center (H j)
    let k := pureFluxOpenResponseRestriction n x
    let B := lemmaVTileHistory Q (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ k)
    let ρ := cubeScaleFactor Q / L.1
    let δ := diagMeshRadius Q (pureFluxBankSourceDepth s) / L.1
    let v := b ^ 2 / σ ^ 2
    Summable (fun j =>
      (fderiv ℝ (modelTraceObservable n ν σ) x (R j)) ^ 2) ∧
    (∑' j, (fderiv ℝ (modelTraceObservable n ν σ) x (R j)) ^ 2) ≤
      4 * v * (rawTraceRemainderB ρ δ) ^ 2 * B ^ 2 *
        (modelTraceObservable n ν σ x) * (modelTraceObservable n ν σ x + 4) := by
  classical
  intro Q L center H R k B ρ δ v
  have htight := raw_trace_model_q3_remainder_bracket_row_tight n s ν σ b hν hσ x
  rcases htight with ⟨hsum, hbound⟩
  have hρ : 0 ≤ cubeScaleFactor (originCube 2 n) /
      (q3ModelLength (n + (s : ℤ))).1 := by
    exact div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos'
      (originCube 2 n)).le (q3ModelLength (n + (s : ℤ))).2.le
  have hδ : 0 ≤ diagMeshRadius (originCube 2 n) (pureFluxBankSourceDepth s) /
      (q3ModelLength (n + (s : ℤ))).1 := by
    exact div_nonneg (diagMeshRadius_pos (originCube 2 n)
      (pureFluxBankSourceDepth s)).le (q3ModelLength (n + (s : ℤ))).2.le
  have hBn : 0 ≤ lemmaVH2Bn
      (cubeScaleFactor (originCube 2 n) / (q3ModelLength (n + (s : ℤ))).1)
      (diagMeshRadius (originCube 2 n) (pureFluxBankSourceDepth s) /
        (q3ModelLength (n + (s : ℤ))).1) := by
    unfold lemmaVH2Bn lemmaVH2R1 lemmaVH2C1 lemmaVH2C2 lemmaVH2A2
    positivity
  have hBsrc := lemmaVH2Bn_le_rawTraceRemainderB hρ hδ
  have hBsquare := pow_le_pow_left₀ hBn hBsrc 2
  have hv : 0 ≤ (b ^ 2 / σ ^ 2) := by positivity
  have hB : 0 ≤ lemmaVTileHistory (originCube 2 n) (pureFluxBankSourceDepth s)
      (responseFramePlanarCoefficientField ν σ
        (pureFluxOpenResponseRestriction n x)) := by
    exact lemmaVTileHistory_nonneg _ _ _
  have hT : 0 ≤ modelTraceObservable n ν σ x :=
    modelTraceObservable_nonneg n ν σ hν hσ x
  have hfactor : 0 ≤ 4 * (b ^ 2 / σ ^ 2) * B ^ 2 *
      modelTraceObservable n ν σ x * (modelTraceObservable n ν σ x + 4) := by
    positivity
  refine ⟨hsum, hbound.trans ?_⟩
  calc
    _ = (4 * (b ^ 2 / σ ^ 2) * B ^ 2 *
        modelTraceObservable n ν σ x * (modelTraceObservable n ν σ x + 4)) *
        lemmaVH2Bn
          (cubeScaleFactor (originCube 2 n) / (q3ModelLength (n + (s : ℤ))).1)
          (diagMeshRadius (originCube 2 n) (pureFluxBankSourceDepth s) /
            (q3ModelLength (n + (s : ℤ))).1) ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hBsquare hfactor
    _ = _ := by ring

/-- The covariance-defect direction in the center/remainder bracket has the
source `κ_f` coefficient in the actual OLD trace coordinates. The response
direction is scaled by the true frame `σ`, exactly as required by Lemma V. -/
theorem raw_trace_model_q3_covariance_defect_bracket_row_tight
    (n : ℤ) (j : ℕ) (ν σ : ℝ) (L : {l : ℝ // 0 < l})
    (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let center := pureFluxParentCenter n
    let k := pureFluxOpenResponseRestriction n x
    let B := lemmaVTileHistory (originCube 2 n) j
      (responseFramePlanarCoefficientField ν σ k)
    let defect : C(closure (cubeSet (originCube 2 n)), ℝ) :=
      ⟨fun y => q3CovarianceDefect L.1 center.1 y.1,
        (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp
          continuous_subtype_val⟩
    let ρ := cubeScaleFactor (originCube 2 n) / L.1
    let δ := diagMeshRadius (originCube 2 n) j / L.1
    |σ * fderiv ℝ (modelTraceObservable n ν σ) x defect| ≤
      2 * lemmaVH2kn ρ δ * B *
        Real.sqrt (modelTraceObservable n ν σ x *
          (modelTraceObservable n ν σ x + 4)) := by
  classical
  intro center k B defect ρ δ
  let Q := originCube 2 n
  let H : ℕ → ResponseCoefficient (openCubeSet Q) := fun l =>
    if l = 0 then σ • pureFluxOpenResponseRestriction n defect
      else (0 : ℝ) • pureFluxOpenResponseRestriction n defect
  have hlink (l : ℕ) :
      (q3CovarianceDefectFamily Q L.1 l).value.toFun =ᵐ[
        volume.restrict (openCubeSet Q)] fun y =>
          responseCoefficientExtension (H l) y / σ := by
    by_cases hl : l = 0
    · subst l
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with y hy
      have hy' : y ∈ openCubeSet (originCube 2 n) := hy
      calc
        (q3CovarianceDefectFamily Q L.1 0).value.toFun y =
            q3CovarianceDefect L.1 (cubeCenter Q) y := by
          simp [q3CovarianceDefectFamily, q3CovarianceDefectWitness,
            PlanarW2Infinity.ofContDiff_value]
        _ = responseCoefficientExtension
            (pureFluxOpenResponseRestriction n defect) y := by
          rw [pureFluxOpenResponseRestriction_value n defect hy']
          rfl
        _ = responseCoefficientExtension (H 0) y / σ := by
          rw [show H 0 = σ • pureFluxOpenResponseRestriction n defect by simp [H],
            responseCoefficientExtension_smul_on _ _ hy']
          simp [hσ.ne']
    · have hzero : l ≠ 0 := hl
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with y hy
      have hy' : y ∈ openCubeSet (originCube 2 n) := hy
      have hleft : (q3CovarianceDefectFamily Q L.1 l).value.toFun y = 0 := by
        simp [q3CovarianceDefectFamily, hzero, PlanarW2Infinity.zero]
      have hright : responseCoefficientExtension (H l) y / σ = 0 := by
        rw [show H l = (0 : ResponseCoefficient (openCubeSet Q)) by simp [H, hzero],
          responseCoefficientExtension_eq (0 : ResponseCoefficient (openCubeSet Q)) hy']
        simp
      rw [hleft, hright]
  have hsingle := nativeSingleTraceBracket n j ν σ hν hσ k L.2 H hlink
  have hdir := hsingle.1 {0} (fun _ : ℕ => 1) (by simp)
  have hdir' :
      |fderiv ℝ (lemmaVTrace n ν σ) k
        (σ • pureFluxOpenResponseRestriction n defect)| ≤
        2 * lemmaVH2kn ρ δ * B *
          Real.sqrt (lemmaVTrace n ν σ k * (lemmaVTrace n ν σ k + 4)) := by
    simpa [H, B, k, Q, ρ, δ, singleDirectionCoefficient] using hdir
  have hderiv := raw_trace_model_fderiv_openRestriction n ν σ hν hσ x defect
  have hscale :
      fderiv ℝ (lemmaVTrace n ν σ) k
          (σ • pureFluxOpenResponseRestriction n defect) =
        σ * fderiv ℝ (modelTraceObservable n ν σ) x defect := by
    rw [map_smul, ← hderiv]
    simp only [smul_eq_mul]
  rw [hscale] at hdir'
  have hT : lemmaVTrace n ν σ k = modelTraceObservable n ν σ x := by
    simpa [k] using
      (modelTraceObservable_eq_lemmaVTrace_openRestriction n ν σ hν hσ x).symm
  simpa [hT] using hdir'


theorem raw_trace_model_q3_covariance_defect_bracket_row
    (n : ℤ) (j : ℕ) (ν σ : ℝ) (L : {l : ℝ // 0 < l})
    (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let center := pureFluxParentCenter n
    let k := pureFluxOpenResponseRestriction n x
    let B := lemmaVTileHistory (originCube 2 n) j
      (responseFramePlanarCoefficientField ν σ k)
    let defect : C(closure (cubeSet (originCube 2 n)), ℝ) :=
      ⟨fun y => q3CovarianceDefect L.1 center.1 y.1,
        (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp
          continuous_subtype_val⟩
    let ρ := cubeScaleFactor (originCube 2 n) / L.1
    let δ := diagMeshRadius (originCube 2 n) j / L.1
    |σ * fderiv ℝ (modelTraceObservable n ν σ) x defect| ≤
      2 * rawTraceRemainderKappaF ρ δ * B *
        Real.sqrt (modelTraceObservable n ν σ x *
          (modelTraceObservable n ν σ x + 4)) := by
  classical
  intro center k B defect ρ δ
  let Q := originCube 2 n
  let H : ℕ → ResponseCoefficient (openCubeSet Q) := fun l =>
    if l = 0 then σ • pureFluxOpenResponseRestriction n defect
      else (0 : ℝ) • pureFluxOpenResponseRestriction n defect
  have hlink (l : ℕ) :
      (q3CovarianceDefectFamily Q L.1 l).value.toFun =ᵐ[
        volume.restrict (openCubeSet Q)] fun y =>
          responseCoefficientExtension (H l) y / σ := by
    by_cases hl : l = 0
    · subst l
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with y hy
      have hy' : y ∈ openCubeSet (originCube 2 n) := hy
      calc
        (q3CovarianceDefectFamily Q L.1 0).value.toFun y =
            q3CovarianceDefect L.1 (cubeCenter Q) y := by
          simp [q3CovarianceDefectFamily, q3CovarianceDefectWitness,
            PlanarW2Infinity.ofContDiff_value]
        _ = responseCoefficientExtension
            (pureFluxOpenResponseRestriction n defect) y := by
          rw [pureFluxOpenResponseRestriction_value n defect hy']
          rfl
        _ = responseCoefficientExtension (H 0) y / σ := by
          rw [show H 0 = σ • pureFluxOpenResponseRestriction n defect by simp [H],
            responseCoefficientExtension_smul_on _ _ hy']
          simp [hσ.ne']
    · have hzero : l ≠ 0 := hl
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with y hy
      have hy' : y ∈ openCubeSet (originCube 2 n) := hy
      have hleft : (q3CovarianceDefectFamily Q L.1 l).value.toFun y = 0 := by
        simp [q3CovarianceDefectFamily, hzero, PlanarW2Infinity.zero]
      have hright : responseCoefficientExtension (H l) y / σ = 0 := by
        rw [show H l = (0 : ResponseCoefficient (openCubeSet Q)) by simp [H, hzero],
          responseCoefficientExtension_eq (0 : ResponseCoefficient (openCubeSet Q)) hy']
        simp
      rw [hleft, hright]
  have hsingle := nativeSingleTraceBracket n j ν σ hν hσ k L.2 H hlink
  have hdir := hsingle.1 {0} (fun _ : ℕ => 1) (by simp)
  have hdir' :
      |fderiv ℝ (lemmaVTrace n ν σ) k
        (σ • pureFluxOpenResponseRestriction n defect)| ≤
        2 * lemmaVH2kn ρ δ * B *
          Real.sqrt (lemmaVTrace n ν σ k * (lemmaVTrace n ν σ k + 4)) := by
    simpa [H, B, k, Q, ρ, δ, singleDirectionCoefficient] using hdir
  have hderiv := raw_trace_model_fderiv_openRestriction n ν σ hν hσ x defect
  have hscale :
      fderiv ℝ (lemmaVTrace n ν σ) k
          (σ • pureFluxOpenResponseRestriction n defect) =
        σ * fderiv ℝ (modelTraceObservable n ν σ) x defect := by
    rw [map_smul, ← hderiv]
    simp only [smul_eq_mul]
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    exact div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le L.2.le
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact div_nonneg (ASDExplicitGamma.Triadic.diagMeshRadius_pos Q j).le L.2.le
  have hκ := lemmaVH2kn_le_rawTraceRemainderKappaF hρ hδ
  have hB0 : 0 ≤ B := lemmaVTileHistory_nonneg Q j
    (responseFramePlanarCoefficientField ν σ k)
  have hroot0 : 0 ≤ Real.sqrt
      (lemmaVTrace n ν σ k * (lemmaVTrace n ν σ k + 4)) :=
    Real.sqrt_nonneg _
  have hfactor : 0 ≤ 2 * B * Real.sqrt
      (lemmaVTrace n ν σ k * (lemmaVTrace n ν σ k + 4)) := by positivity
  have hcoefficient :
      2 * lemmaVH2kn ρ δ * B *
          Real.sqrt (lemmaVTrace n ν σ k * (lemmaVTrace n ν σ k + 4)) ≤
        2 * rawTraceRemainderKappaF ρ δ * B *
          Real.sqrt (lemmaVTrace n ν σ k * (lemmaVTrace n ν σ k + 4)) := by
    calc
      _ = lemmaVH2kn ρ δ *
          (2 * B * Real.sqrt (lemmaVTrace n ν σ k * (lemmaVTrace n ν σ k + 4))) := by ring
      _ ≤ rawTraceRemainderKappaF ρ δ *
          (2 * B * Real.sqrt (lemmaVTrace n ν σ k * (lemmaVTrace n ν σ k + 4))) :=
        mul_le_mul_of_nonneg_right hκ hfactor
      _ = _ := by ring
  have hdirBound := hdir'.trans hcoefficient
  rw [hscale] at hdirBound
  have hT : lemmaVTrace n ν σ k = modelTraceObservable n ν σ x := by
    simpa [k] using
      (modelTraceObservable_eq_lemmaVTrace_openRestriction n ν σ hν hσ x).symm
  simpa [hT] using hdirBound

private theorem raw_trace_q3_center_remainder_vector_tsum
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    let K := closure (cubeSet (originCube 2 n))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let defect : C(K, ℝ) :=
      ⟨fun y => q3CovarianceDefect L.1 center.1 y.1,
        (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp
          continuous_subtype_val⟩
    (∑' j, (H j center) • centeringMap center (H j)) = b ^ 2 • defect := by
  classical
  intro K center H defect
  let R : C(K, ℝ) →L[ℝ] C(K, ℝ) := centeringMap center
  let eval : C(K, ℝ) →L[ℝ] ℝ := ContinuousMap.evalCLM ℝ center
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(K, ℝ) inferInstance (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance (mainCubeQ3Directions n b L)
      (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)
  have hcoeff : Summable (fun j => ‖eval (H j)‖ ^ 2) :=
    summable_sq_norm_map hH eval
  have hrem : Summable (fun j => ‖R (H j)‖ ^ 2) :=
    summable_sq_norm_map hH R
  have hcoeffR : Summable (fun j => ‖eval (H j)‖ ^ (2 : ℝ)) := by
    exact hcoeff.congr (fun j => (Real.rpow_natCast _ _).symm)
  have hremR : Summable (fun j => ‖R (H j)‖ ^ (2 : ℝ)) := by
    exact hrem.congr (fun j => (Real.rpow_natCast _ _).symm)
  have h22 : Real.HolderConjugate (2 : ℝ) 2 := by
    exact (Real.holderConjugate_iff_eq_conjExponent
      (by norm_num : (1 : ℝ) < 2)).2 (by norm_num [Real.conjExponent])
  have hprod : Summable (fun j => ‖eval (H j)‖ * ‖R (H j)‖) :=
    Real.summable_mul_of_Lp_Lq_of_nonneg
      (f := fun j => ‖eval (H j)‖) (g := fun j => ‖R (H j)‖)
      h22 (fun j => norm_nonneg (eval (H j)))
      (fun j => norm_nonneg (R (H j))) hcoeffR hremR
  have hterms : Summable (fun j => (H j center) • R (H j)) := by
    apply Summable.of_norm_bounded hprod
    intro j
    simp [eval, ContinuousMap.evalCLM_apply, norm_smul]
  have hcenter : cubeCenter (originCube 2 n) = 0 := by
    ext i
    simp [cubeCenter, originCube]
  have hpoint (y : K) :
      q3Cov ((0 - y.1 0) / L.1) * q3Cov ((0 - y.1 1) / L.1) - 1 = defect y := by
    have harg0 : (0 - y.1 0) / L.1 = -((y.1 0 - 0) / L.1) := by ring
    have harg1 : (0 - y.1 1) / L.1 = -((y.1 1 - 0) / L.1) := by ring
    change q3Cov ((0 - y.1 0) / L.1) * q3Cov ((0 - y.1 1) / L.1) - 1 =
      q3CovarianceDefect L.1 center.1 y.1
    rw [show center.1 = cubeCenter (originCube 2 n) by rfl, hcenter]
    unfold q3CovarianceDefect ASDExplicitGamma.Model.q3ProductCovariance
    rw [harg0, harg1, ASDExplicitGamma.Model.q3Cov_even,
      ASDExplicitGamma.Model.q3Cov_even]
    rfl
  apply ContinuousMap.ext
  intro y
  have hEval := (ContinuousMap.evalCLM ℝ y).map_tsum hterms
  have hcov := pureFluxMainCubeQ3_parentCenter_remainder_covariance n b L y
  calc
    (∑' j, (H j center) • R (H j)) y =
        ∑' j, ((H j center) • R (H j)) y := by
          simpa only [ContinuousMap.evalCLM_apply] using hEval
    _ = ∑' j, (H j center) * (H j y - H j center) := by
      apply tsum_congr
      intro j
      simp [R, centeringMap_apply, smul_eq_mul]
    _ = b ^ 2 * defect y := by rw [hcov, hpoint]
    _ = (b ^ 2 • defect) y := by simp

/-- The first-derivative center/remainder covariance is the actual q3
product-kernel defect. This identity retains the mixed covariance exactly. -/
theorem raw_trace_model_q3_center_remainder_derivative_identity
    (n : ℤ) (ν σ b : ℝ) (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let K := closure (cubeSet (originCube 2 n))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let R := centeringMap center
    let D := fderiv ℝ (modelTraceObservable n ν σ) x
    let defect : C(K, ℝ) :=
      ⟨fun y => q3CovarianceDefect L.1 center.1 y.1,
        (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp
          continuous_subtype_val⟩
    (∑' j, (H j center) * D (R (H j))) = b ^ 2 * D defect := by
  classical
  intro K center H R D defect
  have hsum : Summable (fun j =>
      (pureFluxMainCubeQ3Directions n b L j
          (pureFluxParentCenter n)) •
        centeringMap (pureFluxParentCenter n)
          (pureFluxMainCubeQ3Directions n b L j)) := by
    -- Rebuild the square-summability estimate for the vector series.
    let H₀ := pureFluxMainCubeQ3Directions n b L
    let c := pureFluxParentCenter n
    let eval : C(K, ℝ) →L[ℝ] ℝ := ContinuousMap.evalCLM ℝ c
    have hH : Summable (fun j => ‖H₀ j‖ ^ 2) := by
      exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
        C(K, ℝ) inferInstance (mainCubeH3InnerProductSpace n b L).toNormedSpace
        inferInstance inferInstance (mainCubeQ3Directions n b L)
        (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)
    have he : Summable (fun j => ‖eval (H₀ j)‖ ^ (2 : ℝ)) := by
      have h := summable_sq_norm_map hH eval
      exact h.congr (fun j => (Real.rpow_natCast _ _).symm)
    have hr : Summable (fun j => ‖centeringMap c (H₀ j)‖ ^ (2 : ℝ)) := by
      have h := summable_sq_norm_map hH (centeringMap c)
      exact h.congr (fun j => (Real.rpow_natCast _ _).symm)
    have h22 : Real.HolderConjugate (2 : ℝ) 2 := by
      exact (Real.holderConjugate_iff_eq_conjExponent
        (by norm_num : (1 : ℝ) < 2)).2 (by norm_num [Real.conjExponent])
    have hp := Real.summable_mul_of_Lp_Lq_of_nonneg
      (f := fun j => ‖eval (H₀ j)‖) (g := fun j => ‖centeringMap c (H₀ j)‖)
      h22 (fun j => norm_nonneg (eval (H₀ j)))
      (fun j => norm_nonneg (centeringMap c (H₀ j))) he hr
    apply Summable.of_norm_bounded hp
    intro j
    simp [eval, ContinuousMap.evalCLM_apply, norm_smul, H₀, c]
  have hvec := raw_trace_q3_center_remainder_vector_tsum n b L
  have hmap := D.map_tsum hsum
  have hpoint (j : ℕ) :
      D ((pureFluxMainCubeQ3Directions n b L j
          (pureFluxParentCenter n)) •
        centeringMap (pureFluxParentCenter n)
          (pureFluxMainCubeQ3Directions n b L j)) =
        (pureFluxMainCubeQ3Directions n b L j
          (pureFluxParentCenter n)) *
          D (centeringMap (pureFluxParentCenter n)
            (pureFluxMainCubeQ3Directions n b L j)) := by
    simp [map_smul, smul_eq_mul]
  calc
    _ = ∑' j, D ((pureFluxMainCubeQ3Directions n b L j
          (pureFluxParentCenter n)) •
        centeringMap (pureFluxParentCenter n)
          (pureFluxMainCubeQ3Directions n b L j)) := by
      apply tsum_congr
      intro j
      exact (hpoint j).symm
    _ = D (∑' j, (pureFluxMainCubeQ3Directions n b L j
          (pureFluxParentCenter n)) •
        centeringMap (pureFluxParentCenter n)
          (pureFluxMainCubeQ3Directions n b L j)) := hmap.symm
    _ = b ^ 2 * D (⟨fun y : K => q3CovarianceDefect L.1
          (pureFluxParentCenter n).1 y.1,
        (q3CovarianceDefect_contDiff L.1
          (pureFluxParentCenter n).1).continuous.comp
          continuous_subtype_val⟩ : C(K, ℝ)) := by
      rw [hvec, map_smul, smul_eq_mul]

/-- Exact full first-gradient-square decomposition into its scalar center,
the retained covariance-defect cross term, and the centered q3 remainder. -/
theorem raw_trace_model_q3_gradient_square_decomposition
    (n : ℤ) (ν σ b : ℝ) (L : {l : ℝ // 0 < l})
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    let K := closure (cubeSet (originCube 2 n))
    let center := pureFluxParentCenter n
    let H := pureFluxMainCubeQ3Directions n b L
    let R := centeringMap center
    let D := fderiv ℝ (modelTraceObservable n ν σ) x
    let defect : C(K, ℝ) :=
      ⟨fun y => q3CovarianceDefect L.1 center.1 y.1,
        (q3CovarianceDefect_contDiff L.1 center.1).continuous.comp
          continuous_subtype_val⟩
    Summable (fun j => (D (H j)) ^ 2) ∧
    modelGradientSquareTrace (modelTraceObservable n ν σ) H x =
      b ^ 2 * (D 1) ^ 2 +
        2 * b ^ 2 * (D 1) * (D defect) +
          ∑' j, (D (R (H j))) ^ 2 := by
  classical
  intro K center H R D defect
  let c : ℕ → ℝ := fun j => H j center
  let r : ℕ → ℝ := fun j => D (R (H j))
  let eval : C(K, ℝ) →L[ℝ] ℝ := ContinuousMap.evalCLM ℝ center
  have hH : Summable (fun j => ‖H j‖ ^ 2) := by
    exact @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(K, ℝ) inferInstance (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance (mainCubeQ3Directions n b L)
      (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)
  have hDsum : Summable (fun j => (D (H j)) ^ 2) := by
    have h := summable_sq_norm_map hH D
    simpa [D] using h
  have hc : Summable (fun j => c j ^ 2) := by
    have h := summable_sq_norm_map hH eval
    simpa [c, eval, ContinuousMap.evalCLM_apply] using h
  have hr : Summable (fun j => r j ^ 2) := by
    have h := summable_sq_norm_map hH (D.comp R)
    simpa [r, ContinuousLinearMap.comp_apply] using h
  have hcR : Summable (fun j => |c j| ^ (2 : ℝ)) := by
    exact hc.congr (fun j => by
      rw [Real.rpow_two]
      exact (sq_abs _).symm)
  have hrR : Summable (fun j => |r j| ^ (2 : ℝ)) := by
    exact hr.congr (fun j => by
      rw [Real.rpow_two]
      exact (sq_abs _).symm)
  have h22 : Real.HolderConjugate (2 : ℝ) 2 := by
    exact (Real.holderConjugate_iff_eq_conjExponent
      (by norm_num : (1 : ℝ) < 2)).2 (by norm_num [Real.conjExponent])
  have hprod : Summable (fun j => |c j| * |r j|) :=
    Real.summable_mul_of_Lp_Lq_of_nonneg
      (f := fun j => |c j|) (g := fun j => |r j|)
      h22 (fun j => abs_nonneg _) (fun j => abs_nonneg _) hcR hrR
  have hcross : Summable (fun j => c j * r j) := by
    apply Summable.of_norm_bounded hprod
    intro j
    simp
  have hvariance := pureFluxMainCubeQ3_parentCenter_variance n b L
  have hcrossValue := raw_trace_model_q3_center_remainder_derivative_identity
    n ν σ b L x
  have hdecomp (j : ℕ) : H j = c j • (1 : C(K, ℝ)) + R (H j) := by
    ext y
    simp [c, R, centeringMap_apply]
  have hderiv (j : ℕ) : D (H j) = c j * D 1 + r j := by
    rw [hdecomp j, map_add, map_smul, smul_eq_mul]
  have hA : Summable (fun j => (D 1) ^ 2 * c j ^ 2) :=
    hc.mul_left ((D 1) ^ 2)
  have hB : Summable (fun j => 2 * (D 1) * (c j * r j)) :=
    hcross.mul_left (2 * D 1)
  have hsumSplit :
      (∑' j, (D (H j)) ^ 2) =
        (∑' j, (D 1) ^ 2 * c j ^ 2) +
          (∑' j, 2 * (D 1) * (c j * r j)) +
            ∑' j, r j ^ 2 := by
    calc
      _ = ∑' j, ((D 1) ^ 2 * c j ^ 2 +
          (2 * (D 1) * (c j * r j) + r j ^ 2)) := by
        apply tsum_congr
        intro j
        rw [hderiv j]
        ring
      _ = (∑' j, (D 1) ^ 2 * c j ^ 2) +
          (∑' j, 2 * (D 1) * (c j * r j)) + ∑' j, r j ^ 2 := by
        calc
          _ = (∑' j, (D 1) ^ 2 * c j ^ 2) +
              ∑' j, (2 * (D 1) * (c j * r j) + r j ^ 2) :=
            hA.tsum_add (hB.add hr)
          _ = _ := by rw [hB.tsum_add hr]; ring
  have hvariance' : (∑' j, c j ^ 2) = b ^ 2 := by
    simpa [c, H, center] using hvariance
  have hcross' : (∑' j, c j * r j) = b ^ 2 * D defect := by
    simpa [c, r, H, center, R, D, defect] using hcrossValue
  refine ⟨?_, ?_⟩
  · exact hDsum
  · rw [modelGradientSquareTrace, hsumSplit]
    rw [show (∑' j, (D 1) ^ 2 * c j ^ 2) = (D 1) ^ 2 * (∑' j, c j ^ 2) by
      rw [tsum_mul_left]]
    rw [show (∑' j, 2 * (D 1) * (c j * r j)) =
      2 * (D 1) * (∑' j, c j * r j) by rw [tsum_mul_left]]
    rw [hvariance', hcross']
    ring

end
end ASDExplicitGamma.Inverse
