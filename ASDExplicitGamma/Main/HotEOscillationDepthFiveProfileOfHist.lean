module

public import ASDExplicitGamma.Main.HotEOscillationDepthFiveProfile
public import ASDExplicitGamma.Main.EOscillationCellHistoryTranslationOfHist
public import ASDExplicitGamma.Main.EOscillationDepthFiveProfileOfHist
public import ASDExplicitGamma.Main.MultiplierMomentsOfHist

/-! Successors of `HotEOscillationDepthFiveProfile` declarations with the history envelope as a parameter `Hfun`. -/



@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff

noncomputable section


/-- Successor of `main_eosc_depth_five_shifted_joint_profile_hot` with the history envelope `Hfun`. -/
theorem main_eosc_depth_five_shifted_joint_profile_hot_ofHist
    (L : {l : ℝ // 0 < l}) (hobs : ℕ)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hL : cubeScaleFactor (originCube 2 (m + hobs)) / (3 : ℝ) ^ (hobs + 5) * (3 : ℝ) ^ 6 ≤ L.1)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (b : ℝ) (hb : 0 < b)
    (Hfun : ℝ → ℝ)
    (hHist : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω < ⊤) ∧
      MemLp (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω => (mainOrdinaryTraceMaxHistory M m (originCube 2 (m - 5)) s ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ Hfun s)
    :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let H := Hfun t
    MemLp (mainEoscDepthFiveShiftedJointProfileHot L hobs M m t b) 2 μ ∧
      lpNorm (mainEoscDepthFiveShiftedJointProfileHot L hobs M m t b) 2 μ ≤
        mainLoadQ H (mainOp (b ^ 2)) (mainOm (b ^ 2)) := by
  classical
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Q : TriadicCube 2 := originCube 2 (m + hobs)
  let D := descendantsAtDepth Q (hobs + 5)
  let H : ℝ := Hfun t
  let op : ℝ := mainOp (b ^ 2)
  let om : ℝ := mainOm (b ^ 2)
  let C : ℝ := (mainBeta + 1) ^ 2 * op ^ 2 +
      mainBeta * mainM0 H * om ^ 2
  let B : TriadicCube 2 → CutoffSample 2 → ℝ := fun U ω =>
    mainEoscShiftedCellInverse M m t U ω
  let M_U : TriadicCube 2 → CutoffSample 2 → ℝ := fun U ω =>
    mainEoscShiftedCellResponse M m t U ω
  let Bplus : TriadicCube 2 → CutoffSample 2 → ℝ := fun U ω => B U ω + 1
  let rad : TriadicCube 2 → CutoffSample 2 → ℝ := fun U ω =>
    (Bplus U ω) ^ 2 *
        oldSignedFlatOscillationSize Q U b L true ^ 2 +
      B U ω * M_U U ω *
        oldSignedFlatOscillationSize Q U b L false ^ 2
  let cell : TriadicCube 2 → CutoffSample 2 → ℝ := fun U ω =>
    if U ∈ D then rad U ω else 0
  let Z : CutoffSample 2 → ℝ := fun ω => descendantsAverage Q (hobs + 5) (fun U => cell U ω)
  let Y : CutoffSample 2 → ℝ := fun ω => Real.sqrt (Z ω)

  have hBeta : 0 ≤ mainBeta := by norm_num [mainBeta]
  have hOne : MemLp (fun _ : CutoffSample 2 => (1 : ℝ)) 2 μ := memLp_const (1 : ℝ)
  have hOneNorm : lpNorm (fun _ : CutoffSample 2 => (1 : ℝ)) 2 μ = 1 := by simp
  have hcellData (U : TriadicCube 2) :
      MemLp (B U) 2 μ ∧ lpNorm (B U) 2 μ ≤ mainBeta ∧
      MemLp (M_U U) 2 μ ∧ lpNorm (M_U U) 2 μ ≤ mainM0 H := by
    rcases main_eosc_shifted_carrier_moments_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ m hpast t ht U with
      ⟨hB, hBcap, hMmem, hMcap⟩
    refine ⟨?_, hBcap, ?_, hMcap⟩
    · simpa only [B, mainEoscShiftedCellInverse] using hB
    · change MemLp (mainPartialInsertedMultiplierHistory M m t ∘
        (fun ω => Cutoff.translateCutoffSample (triadicCubeShift U) ω)) 2 μ
      simpa only [M_U, mainEoscShiftedCellResponse] using hMmem

  have hcellProduct (U : TriadicCube 2) :
      (∫ ω, B U ω * M_U U ω ∂μ) ≤ mainBeta * mainM0 H := by
    simpa only [B, M_U, mainEoscShiftedCellInverse,
      mainEoscShiftedCellResponse, H, μ, Function.comp_apply] using
      main_eosc_shifted_carrier_product_moment_ofHist (Hfun := Hfun) (hHist := hHist) M h hM hγ m hpast t ht U

  have hBplusData (U : TriadicCube 2) :
      MemLp (Bplus U) 2 μ ∧ lpNorm (Bplus U) 2 μ ≤ mainBeta + 1 := by
    have hBU := hcellData U
    have hBplusMem : MemLp (Bplus U) 2 μ := by
      change MemLp (B U + fun _ => (1 : ℝ)) 2 μ
      exact hBU.1.add hOne
    have hnorm : lpNorm (Bplus U) 2 μ ≤ mainBeta + 1 := by
      change lpNorm (B U + fun _ => (1 : ℝ)) 2 μ ≤ mainBeta + 1
      calc
        lpNorm (B U + fun _ => (1 : ℝ)) 2 μ ≤
            lpNorm (B U) 2 μ + lpNorm (fun _ : CutoffSample 2 => (1 : ℝ)) 2 μ :=
          lpNorm_add_le hBU.1 (by norm_num : 1 ≤ (2 : ENNReal))
        _ ≤ mainBeta + 1 := by
          exact add_le_add hBU.2.1 (by simp)
    exact ⟨by simpa only [Bplus] using hBplusMem,
      by simpa only [Bplus] using hnorm⟩

  have hBplusMoment (U : TriadicCube 2) :
      (∫ ω, (Bplus U ω) ^ 2 ∂μ) ≤ (mainBeta + 1) ^ 2 := by
    have hdata := hBplusData U
    have hsq := mul_le_mul hdata.2 hdata.2
      (lpNorm_nonneg (f := Bplus U) (p := 2) (μ := μ)) (by positivity)
    calc
      (∫ ω, (Bplus U ω) ^ 2 ∂μ) = lpNorm (Bplus U) 2 μ ^ 2 := by
        symm
        exact ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hdata.1
      _ ≤ (mainBeta + 1) ^ 2 := by simpa only [pow_two] using hsq

  have hradInt (U : TriadicCube 2) : Integrable (rad U) μ := by
    let p : ℝ := oldSignedFlatOscillationSize Q U b L true
    let q : ℝ := oldSignedFlatOscillationSize Q U b L false
    have hp : Integrable (fun ω => (Bplus U ω) ^ 2) μ := by
      exact (memLp_two_iff_integrable_sq (hBplusData U).1.aestronglyMeasurable).mp
        (hBplusData U).1
    have hmul : Integrable (fun ω => B U ω * M_U U ω) μ :=
      (hcellData U).1.integrable_mul (hcellData U).2.2.1
    change Integrable (fun ω => (Bplus U ω) ^ 2 * p ^ 2 +
      (B U ω * M_U U ω) * q ^ 2) μ
    convert (hp.const_mul (p ^ 2)).add (hmul.const_mul (q ^ 2)) using 1
    ext ω
    simp [p, q, mul_assoc, mul_comm]

  have hradCap (U : TriadicCube 2) : (∫ ω, rad U ω ∂μ) ≤
      (mainBeta + 1) ^ 2 *
          oldSignedFlatOscillationSize Q U b L true ^ 2 +
        mainBeta * mainM0 H *
          oldSignedFlatOscillationSize Q U b L false ^ 2 := by
    let p : ℝ := oldSignedFlatOscillationSize Q U b L true
    let q : ℝ := oldSignedFlatOscillationSize Q U b L false
    have hpInt : Integrable (fun ω => p ^ 2 * (Bplus U ω) ^ 2) μ :=
      (memLp_two_iff_integrable_sq (hBplusData U).1.aestronglyMeasurable).mp
        (hBplusData U).1 |>.const_mul (p ^ 2)
    have hmulInt : Integrable (fun ω => q ^ 2 * (B U ω * M_U U ω)) μ :=
      ((hcellData U).1.integrable_mul (hcellData U).2.2.1).const_mul (q ^ 2)
    have hEq : rad U = fun ω => p ^ 2 * (Bplus U ω) ^ 2 +
        q ^ 2 * (B U ω * M_U U ω) := by
      funext ω
      dsimp [rad, Bplus, p, q]
      ring
    rw [hEq, integral_add hpInt hmulInt, integral_const_mul, integral_const_mul]
    calc
      p ^ 2 * (∫ ω, (Bplus U ω) ^ 2 ∂μ) +
          q ^ 2 * (∫ ω, B U ω * M_U U ω ∂μ) ≤
        p ^ 2 * (mainBeta + 1) ^ 2 + q ^ 2 *
          (mainBeta * mainM0 H) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hBplusMoment U) (sq_nonneg p))
              (mul_le_mul_of_nonneg_left (hcellProduct U) (sq_nonneg q))
      _ = (mainBeta + 1) ^ 2 * p ^ 2 +
          mainBeta * mainM0 H * q ^ 2 := by ring

  have hradNonneg : ∀ᵐ ω ∂μ, 0 ≤ Z ω := by
    have hMNonneg : ∀ U, 0 ≤ᵐ[μ] M_U U := by
      intro U
      have hMom := main_multiplier_moments_of_main_envelope_h_ofHist (Hfun := Hfun) (hHist := hHist)
        M h hM hγ m hpast t ht.1 ht.2
      have hmp : MeasurePreserving
          (fun ω : CutoffSample 2 => Cutoff.translateCutoffSample
            (triadicCubeShift U) ω) μ μ := by
        exact ⟨Cutoff.measurable_translateCutoffSample (triadicCubeShift U),
          Cutoff.map_translateCutoffSample_cutoffSampleLaw M (triadicCubeShift U)⟩
      change 0 ≤ᵐ[μ]
        (mainPartialInsertedMultiplierHistory M m t ∘
          fun ω => Cutoff.translateCutoffSample (triadicCubeShift U) ω)
      exact hmp.quasiMeasurePreserving.ae hMom.2
    have hfinite := ae_all_iff.mpr hMNonneg
    filter_upwards [hfinite] with ω hω
    apply descendantsAverage_nonneg
    intro U hU
    simp [cell]
    have hB0 : 0 ≤ B U ω := by
      dsimp [B, mainEoscShiftedCellInverse]
      positivity
    have hM0' : 0 ≤ M_U U ω := hω U
    dsimp [rad]
    positivity

  have hcellInt (U : TriadicCube 2) (hU : U ∈ D) : Integrable (cell U) μ := by
    simp [cell, hU]
    exact hradInt U
  have hsumInt : Integrable (fun ω => ∑ U ∈ D, cell U ω) μ :=
    integrable_finsetSum D (fun U hU => hcellInt U hU)
  have hZint : Integrable Z μ := by
    change Integrable (fun ω => ((D.card : ℝ)⁻¹) *
      ∑ U ∈ D, cell U ω) μ
    exact hsumInt.const_mul _
  have hZEq : (∫ ω, Z ω ∂μ) = descendantsAverage Q (hobs + 5)
      (fun U => ∫ ω, rad U ω ∂μ) := by
    rw [show Z = fun ω => ((D.card : ℝ)⁻¹) * ∑ U ∈ D, cell U ω by
      funext ω
      rfl]
    rw [integral_const_mul, integral_finsetSum D
      (fun U hU => hcellInt U hU)]
    unfold descendantsAverage
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    have hcellEq : cell U = rad U := by
      funext ω
      simp [cell, hU]
    rw [hcellEq]

  have hOpCap := main_hot_flatPlus_descendant_average_le_mainOp_sq
    Q (hobs + 5) b L hL
  have hOmCap := main_hot_flatMinus_descendant_average_le_mainOm_sq
    Q (hobs + 5) b L hL
  have hM0 : 0 ≤ mainM0 H := by
    have hnorm := lpNorm_nonneg (f := M_U (originCube 2 m)) (p := 2) (μ := μ)
    exact le_trans hnorm (hcellData (originCube 2 m)).2.2.2
  have hZCap : (∫ ω, Z ω ∂μ) ≤ C := by
    rw [hZEq]
    calc
      descendantsAverage Q (hobs + 5) (fun U => ∫ ω, rad U ω ∂μ) ≤
          descendantsAverage Q (hobs + 5) (fun U =>
            (mainBeta + 1) ^ 2 *
                oldSignedFlatOscillationSize Q U b L true ^ 2 +
              mainBeta * mainM0 H *
                oldSignedFlatOscillationSize Q U b L false ^ 2) :=
        descendantsAverage_le (fun U _ => hradCap U)
      _ = (mainBeta + 1) ^ 2 *
            descendantsAverage Q (hobs + 5) (fun U =>
              oldSignedFlatOscillationSize Q U b L true ^ 2) +
          mainBeta * mainM0 H * descendantsAverage Q (hobs + 5) (fun U =>
            oldSignedFlatOscillationSize Q U b L false ^ 2) := by
        rw [descendantsAverage_add, descendantsAverage_mul_left,
          descendantsAverage_mul_left]
      _ ≤ C := by
        dsimp [C, op, om]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hOpCap (by positivity))
          (mul_le_mul_of_nonneg_left hOmCap (mul_nonneg hBeta hM0))

  have hYsq : (fun ω => Y ω ^ 2) =ᵐ[μ] Z := by
    filter_upwards [hradNonneg] with ω hω
    exact Real.sq_sqrt hω
  have hYsqInt : Integrable (fun ω => Y ω ^ 2) μ := by
    exact hZint.congr hYsq.symm
  have hYmeas : AEStronglyMeasurable Y μ := by
    change AEStronglyMeasurable (fun ω => Real.sqrt (Z ω)) μ
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hZint.aestronglyMeasurable
  have hYmem : MemLp Y 2 μ := (memLp_two_iff_integrable_sq hYmeas).2 hYsqInt
  have hnormSq := ASDExplicitGamma.Gaussian.rio_lpNorm_two_sq hYmem
  have hCsqNonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hCsqrt : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
  have hYIntegral : (∫ ω, Y ω ^ 2 ∂μ) = ∫ ω, Z ω ∂μ :=
    integral_congr_ae hYsq
  have hSqCap : lpNorm Y 2 μ ^ 2 ≤ (Real.sqrt C) ^ 2 := by
    rw [hnormSq, hYIntegral]
    simpa only [Real.sq_sqrt hCsqNonneg] using hZCap
  have hnormCap : lpNorm Y 2 μ ≤ Real.sqrt C :=
    (sq_le_sq₀ (lpNorm_nonneg (f := Y) (p := 2) (μ := μ)) hCsqrt).mp hSqCap
  have hLoadQ : Real.sqrt C = mainLoadQ H op om := by
    simp [C, op, om, mainLoadQ]
  change MemLp Y 2 μ ∧ lpNorm Y 2 μ ≤ mainLoadQ H op om
  exact ⟨by simpa only [Y] using hYmem,
    by rw [← hLoadQ]; simpa only [Y] using hnormCap⟩

end
end ASDExplicitGamma.Main
end
