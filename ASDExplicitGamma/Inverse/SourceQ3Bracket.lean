module

public import ASDExplicitGamma.Inverse.RawShellQ3Bracket

/-! Actual source brackets with the canonical single and remainder coefficients.
Adapted from RawShellQ3Bracket, omitting only the outward coefficient weakening. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
noncomputable section

theorem source_model_q3_remainder_bracket_row
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
  have hcoeff : (Real.sqrt (b ^ 2) * lemmaVH2Bn ρ δ) ^ 2 / σ ^ 2 ≤
      (b ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (sq_nonneg b)]
    exact le_of_eq (by ring)
  have hT0 : 0 ≤ modelTraceObservable n ν σ x :=
    modelTraceObservable_nonneg n ν σ hν hσ x
  have hB0 : 0 ≤ B := lemmaVTileHistory_nonneg Q
    (pureFluxBankSourceDepth s)
    (responseFramePlanarCoefficientField ν σ k)
  have hC : 0 ≤ 4 * B ^ 2 * modelTraceObservable n ν σ x *
      (modelTraceObservable n ν σ x + 4) := by positivity
  refine ⟨hsum, hnative.trans ?_⟩
  calc
    (4 * (Real.sqrt (b ^ 2) * lemmaVH2Bn ρ δ) ^ 2 * B ^ 2 *
        modelTraceObservable n ν σ x * (modelTraceObservable n ν σ x + 4)) /
        σ ^ 2 =
      (4 * B ^ 2 * modelTraceObservable n ν σ x *
        (modelTraceObservable n ν σ x + 4)) *
        ((Real.sqrt (b ^ 2) * lemmaVH2Bn ρ δ) ^ 2 / σ ^ 2) := by ring
    _ ≤ (4 * B ^ 2 * modelTraceObservable n ν σ x *
        (modelTraceObservable n ν σ x + 4)) *
        ((b ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2) :=
      mul_le_mul_of_nonneg_left hcoeff hC
    _ = 4 * (b ^ 2 / σ ^ 2) * (lemmaVH2Bn ρ δ) ^ 2 *
        B ^ 2 * modelTraceObservable n ν σ x *
          (modelTraceObservable n ν σ x + 4) := by ring

/-- The covariance-defect direction in the center/remainder bracket has the
source `κ_f` coefficient in the actual OLD trace coordinates. The response
direction is scaled by the true frame `σ`, exactly as required by Lemma V. -/
theorem source_model_q3_covariance_defect_bracket_row
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
  have hρ : 0 ≤ ρ := by
    dsimp [ρ]
    exact div_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le L.2.le
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact div_nonneg (ASDExplicitGamma.Triadic.diagMeshRadius_pos Q j).le L.2.le
  have hdirBound := hdir'
  rw [hscale] at hdirBound
  have hT : lemmaVTrace n ν σ k = modelTraceObservable n ν σ x := by
    simpa [k] using
      (modelTraceObservable_eq_lemmaVTrace_openRestriction n ν σ hν hσ x).symm
  simpa [hT] using hdirBound

end
end ASDExplicitGamma.Inverse
