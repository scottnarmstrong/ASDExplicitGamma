module

public import ASDExplicitGamma.Main.EOscillationDepthFiveProfile
public import ASDExplicitGamma.Main.HotFlatProfile
public import ASDExplicitGamma.Main.HotEOscillationCellTranslation
public import ASDExplicitGamma.Main.EOscillationCellHistoryTranslation
public import ASDExplicitGamma.Main.EOscillationCellFamily
public import ASDExplicitGamma.Main.EOscillationJointProfile
public import ASDExplicitGamma.Main.EOscillationFlatOscillationCaps
public import ASDExplicitGamma.Native.OldSignedCenteredPositive
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The source-cell joint oscillation profile has its explicit `mainLoadQ`
second-moment cap after translating each depth-five cell separately. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
open ASDExplicitGamma.Native ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff

noncomputable section


theorem hot_cell_scale_hot (m : ℤ) (hobs : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5)) :
    U.scale = m - 5 := by
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
  dsimp only [originCube] at hs ⊢
  push_cast at hs
  omega

/-- The cellwise D-main joint oscillation radicand, with the local histories
replaced by the translated singleton-root bank carriers. Flat oscillation
sizes are deterministic source-cell quantities. -/
noncomputable def mainEoscShiftedCellJointRadicandHot
    (L : {l : ℝ // 0 < l}) (hobs : ℕ)
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (U : TriadicCube 2)
    (b : ℝ) (ω : CutoffSample 2) : ℝ :=
  (mainEoscShiftedCellInverse M m t U ω + 1) ^ 2 *
      oldSignedFlatOscillationSize (originCube 2 (m + hobs)) U b
        L true ^ 2 +
    mainEoscShiftedCellInverse M m t U ω *
      mainEoscShiftedCellResponse M m t U ω *
        oldSignedFlatOscillationSize (originCube 2 (m + hobs)) U b
          L false ^ 2

/-- The actual OLD local joint profile on a depth-five source cell. -/
noncomputable def mainEoscLocalJointProfileHot
    (L : {l : ℝ // 0 < l}) (hobs : ℕ)
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (U : TriadicCube 2)
    (b : ℝ) (ω : CutoffSample 2) : ℝ :=
  let a := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ)
    (mainInsertionSkewCoefficient m t U ω)
  Real.sqrt
    ((oldSignedInverseHistory U a + 1) ^ 2 *
        oldSignedFlatOscillationSize (originCube 2 (m + hobs)) U b
          L true ^ 2 +
      oldSignedInverseHistory U a * oldSignedResponseHistory U a *
        oldSignedFlatOscillationSize (originCube 2 (m + hobs)) U b
          L false ^ 2)

/-- The root-mean-square translated profile over the complete depth-five
source tiling. -/
noncomputable def mainEoscDepthFiveShiftedJointProfileHot
    (L : {l : ℝ // 0 < l}) (hobs : ℕ)
    (M : ABKModel 2) (m : ℤ) (t b : ℝ) (ω : CutoffSample 2) : ℝ :=
  Real.sqrt (descendantsAverage (originCube 2 (m + hobs)) (hobs + 5) (fun U =>
    if U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5) then
      mainEoscShiftedCellJointRadicandHot L hobs M m t U b ω
    else 0))

/-- The root-coefficient joint oscillation profile used in the exact `2dq`
row, averaged over the depth-five source cells. -/
noncomputable def mainEoscDepthFiveActualJointProfileHot
    (L : {l : ℝ // 0 < l}) (hobs : ℕ)
    (M : ABKModel 2) (m : ℤ) (t b : ℝ) (ω : CutoffSample 2) : ℝ :=
  let Q : TriadicCube 2 := originCube 2 (m + hobs)
  let k := mainInsertionSkewCoefficient m t Q ω
  Real.sqrt (descendantsAverage Q (hobs + 5) (fun U =>
    mainOldJointOscillationProfile Q U M.nu (Annealed.sigmaBar M m : ℝ)
      k b L ^ 2))

/-- On each source cell, the actual local histories are dominated by the
translated inverse-bank and multiplier histories. This is an a.e. statement
with a cell-dependent shift, so no common sibling-cell pathwise maximum is
asserted. -/
theorem main_eosc_local_joint_profile_sq_le_shifted_hot
    (L : {l : ℝ // 0 < l}) (hobs : ℕ)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hL : cubeScaleFactor (originCube 2 (m + hobs)) / (3 : ℝ) ^ (hobs + 5) * (3 : ℝ) ^ 6 ≤ L.1)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 (m + hobs)) (hobs + 5))
    (b : ℝ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainEoscLocalJointProfileHot L hobs M m t U b ω ^ 2 ≤
        mainEoscShiftedCellJointRadicandHot L hobs M m t U b ω := by
  have hshift := main_eosc_local_shifted_carrier_hot M h hM hγ m hpast t ht U (hot_cell_scale_hot m hobs U hU)
  filter_upwards [hshift] with ω hω
  let a := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ) (mainInsertionSkewCoefficient m t U ω)
  let I := oldSignedInverseHistory U a
  let R := oldSignedResponseHistory U a
  let B := mainEoscShiftedCellInverse M m t U ω
  let M_U := mainEoscShiftedCellResponse M m t U ω
  have hIle : I ≤ B := by
    simpa only [I, a, B, mainEoscShiftedCellInverse] using hω.1
  have hReq : R = M_U := by
    simpa only [R, a, M_U, mainEoscShiftedCellResponse] using hω.2
  have hI0 : 0 ≤ I := by
    dsimp [I, a, oldSignedInverseHistory]
    exact lemmaVInverseHistory_nonneg U _
      (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hR0 : 0 ≤ R := by
    dsimp [R, oldSignedResponseHistory]
    exact ENNReal.toReal_nonneg
  have hB0 : 0 ≤ B := by dsimp [B, mainEoscShiftedCellInverse]; positivity
  have hM0 : 0 ≤ M_U := by rw [← hReq]; exact hR0
  have hBplus : I + 1 ≤ B + 1 := by linarith
  have hPlusSq : (I + 1) ^ 2 ≤ (B + 1) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hBplus
  have hIR : I * R ≤ B * M_U := by
    calc
      I * R ≤ B * R := mul_le_mul_of_nonneg_right hIle hR0
      _ = B * M_U := by rw [hReq]
  have hOscPlus0 : 0 ≤ oldSignedFlatOscillationSize (originCube 2 (m + hobs)) U b
      L true := Real.sqrt_nonneg _
  have hOscMinus0 : 0 ≤ oldSignedFlatOscillationSize (originCube 2 (m + hobs)) U b
      L false := Real.sqrt_nonneg _
  have hrad : 0 ≤ (I + 1) ^ 2 *
      oldSignedFlatOscillationSize (originCube 2 (m + hobs)) U b
        L true ^ 2 +
      I * R * oldSignedFlatOscillationSize (originCube 2 (m + hobs)) U b
        L false ^ 2 := by positivity
  have hlocalSq : mainEoscLocalJointProfileHot L hobs M m t U b ω ^ 2 =
      (I + 1) ^ 2 * oldSignedFlatOscillationSize (originCube 2 (m + hobs)) U b
        L true ^ 2 +
      I * R * oldSignedFlatOscillationSize (originCube 2 (m + hobs)) U b
        L false ^ 2 := by
    simp [mainEoscLocalJointProfileHot, a, I, R, Real.sq_sqrt hrad]
  rw [hlocalSq]
  change (I + 1) ^ 2 * _ + I * R * _ ≤
    (B + 1) ^ 2 * _ + B * M_U * _
  exact add_le_add
    (mul_le_mul_of_nonneg_right hPlusSq (sq_nonneg _))
    (mul_le_mul_of_nonneg_right hIR (sq_nonneg _))

/-- The actual-law depth-five RMS of the cellwise joint oscillation profile
has the explicit `mainLoadQ` cap. The proof translates each source cell to
its own origin sample, retains the joint inverse/response moment there, and
uses the deterministic descendant oscillation caps only after averaging. -/
theorem main_eosc_depth_five_shifted_joint_profile_hot
    (L : {l : ℝ // 0 < l}) (hobs : ℕ)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hL : cubeScaleFactor (originCube 2 (m + hobs)) / (3 : ℝ) ^ (hobs + 5) * (3 : ℝ) ^ 6 ≤ L.1)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (b : ℝ) (hb : 0 < b) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    let H := mainEnvelopeH (theta M) M.gamma t
    MemLp (mainEoscDepthFiveShiftedJointProfileHot L hobs M m t b) 2 μ ∧
      lpNorm (mainEoscDepthFiveShiftedJointProfileHot L hobs M m t b) 2 μ ≤
        mainLoadQ H (mainOp (b ^ 2)) (mainOm (b ^ 2)) := by
  classical
  dsimp only
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Q : TriadicCube 2 := originCube 2 (m + hobs)
  let D := descendantsAtDepth Q (hobs + 5)
  let H : ℝ := mainEnvelopeH (theta M) M.gamma t
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
    rcases main_eosc_shifted_carrier_moments M h hM hγ m hpast t ht U with
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
      main_eosc_shifted_carrier_product_moment M h hM hγ m hpast t ht U

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
      have hMom := main_multiplier_moments_of_main_envelope_h
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

/-- The exact root-coefficient profile in the oscillation carrier is
pointwise dominated, after the depth-five spatial average, by the translated
profile whose `mainLoadQ` second-moment cap is proved above. The coefficient
restriction and history congruence are both used cell by cell. -/
theorem main_eosc_actual_joint_profile_rms_le_shifted_hot
    (L : {l : ℝ // 0 < l}) (hobs : ℕ)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hL : cubeScaleFactor (originCube 2 (m + hobs)) / (3 : ℝ) ^ (hobs + 5) * (3 : ℝ) ^ 6 ≤ L.1)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (b : ℝ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainEoscDepthFiveActualJointProfileHot L hobs M m t b ω ≤
        mainEoscDepthFiveShiftedJointProfileHot L hobs M m t b ω := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Q : TriadicCube 2 := originCube 2 (m + hobs)
  let D := descendantsAtDepth Q (hobs + 5)
  have hcell (U : TriadicCube 2) (hU : U ∈ D) :
      ∀ᵐ ω ∂μ,
        mainOldJointOscillationProfile Q U M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t Q ω) b
            L ^ 2 ≤
          mainEoscShiftedCellJointRadicandHot L hobs M m t U b ω := by
    let hsub : openCubeSet U ⊆ openCubeSet Q :=
      openCubeSet_subset_of_mem_descendantsAtDepth hU
    have hσ : 0 < (Annealed.sigmaBar M m : ℝ) :=
      (Annealed.sigmaBar_characterization M m).1
    have hk (ω : CutoffSample 2) :=
      mainInsertionSkewCoefficient_cell_eq Q U hsub m t ω
    have hhist (ω : CutoffSample 2) := old_signed_cell_histories Q U hsub M.nu
      (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
      (mainInsertionSkewCoefficient m t Q ω)
    have hInv (ω : CutoffSample 2) :
        oldSignedInverseHistory U
            (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M m : ℝ)
              (mainInsertionSkewCoefficient m t Q ω)) =
          oldSignedInverseHistory U
            (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M m : ℝ)
              (mainInsertionSkewCoefficient m t U ω)) := by
      have hh := (hhist ω).1
      rw [hk ω] at hh
      exact hh.symm
    have hResp (ω : CutoffSample 2) :
        oldSignedResponseHistory U
            (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M m : ℝ)
              (mainInsertionSkewCoefficient m t Q ω)) =
          oldSignedResponseHistory U
            (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M m : ℝ)
              (mainInsertionSkewCoefficient m t U ω)) := by
      have hh := (hhist ω).2.1
      rw [hk ω] at hh
      exact hh.symm
    have hprofile (ω : CutoffSample 2) :
        mainOldJointOscillationProfile Q U M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t Q ω) b
            L =
          mainEoscLocalJointProfileHot L hobs M m t U b ω := by
      simp [mainOldJointOscillationProfile,
        mainEoscLocalJointProfileHot, hInv ω, hResp ω, Q]
    filter_upwards
      [main_eosc_local_joint_profile_sq_le_shifted_hot
        L hobs M h hM hγ m hL hpast t ht U hU b] with ω hω
    rw [hprofile ω]
    exact hω
  have hcell' (U : TriadicCube 2) :
      ∀ᵐ ω ∂μ,
        (if hU : U ∈ D then
          mainOldJointOscillationProfile Q U M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t Q ω) b
            L ^ 2 ≤
          mainEoscShiftedCellJointRadicandHot L hobs M m t U b ω
        else True) := by
    by_cases hU : U ∈ D
    · filter_upwards [hcell U hU] with ω hω
      simpa only [dif_pos hU] using hω
    · filter_upwards with ω
      simp [hU]
  have hall := ae_all_iff.mpr hcell'
  filter_upwards [hall] with ω hω
  change Real.sqrt (descendantsAverage Q (hobs + 5) (fun U =>
      mainOldJointOscillationProfile Q U M.nu
        (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t Q ω) b
        L ^ 2)) ≤
    Real.sqrt (descendantsAverage Q (hobs + 5) (fun U =>
      if U ∈ D then mainEoscShiftedCellJointRadicandHot L hobs M m t U b ω else 0))
  apply Real.sqrt_le_sqrt
  apply descendantsAverage_le
  intro U hU
  have hUD : U ∈ D := hU
  have hh := hω U
  have hrad := (show
      mainOldJointOscillationProfile Q U M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t Q ω) b
          L ^ 2 ≤
        mainEoscShiftedCellJointRadicandHot L hobs M m t U b ω by
    simpa only [dif_pos hUD] using hh)
  simpa only [if_pos hUD] using hrad

end
end ASDExplicitGamma.Main
