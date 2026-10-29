/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackActualCharges
public import ASDExplicitGamma.Scalar.SmoothFeedbackLoadOscillation

/-! The consumer hypotheses of the smooth-feedback estimate, instantiated on
the actual OLD objects of the shell `k = m + 1`: the cutoff law, the OLD
maximizers, the actual cell responses, the OLD bank for `𝓑` and the `L²`
moment of the cell histories. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Main ASDExplicitGamma.Inverse
open ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3
open scoped BigOperators ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

/-- The envelope bound `Ξ₀ ≤ ξ` of the shell `k = m + 1`. -/
def xi'' (M : ABKModel 2) (h : ℝ) (m : ℤ) : ℝ :=
  mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) / (Annealed.sigmaBar M m : ℝ)) ^ 2)
    M.gamma mainSourceInversePrefix (theta M) 0

theorem xi_nonneg (M : ABKModel 2) (h : ℝ) (hγ : M.gamma ≤ gammaZero) (m : ℤ) :
    0 ≤ xi'' M h m := by
  have hg0 := M.shellPrefix.gamma_pos.le
  have hθ : 0 ≤ theta M := div_nonneg hg0 (by unfold gammaZero; norm_num)
  have h1 := mainEnvelopeXi_ge_initial (v := (q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2) (gamma := M.gamma) (xiPre := mainSourceInversePrefix)
    (theta := theta M) (t := 0) (sq_nonneg _) hg0 hγ hθ le_rfl
  have h2 := mainSourceInversePrefix_gate
  unfold mainBetaOld at h2
  unfold xi''
  linarith

/-- The centered quarter regularity of the actual loads on every child cell. -/
theorem hcenter'' {ι : Type*} (Q : TriadicCube 2) (u : ι → H10Function (openCubeSet Q))
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function) (depth : ℕ) :
    ∀ i, ∀ U : TriadicCube 2, U ∈ descendantsAtDepth Q depth →
      ScalarPositiveHaarAdmissible U (fun x j =>
        (u i).toH1Function.grad x j -
          cubeAverage U (fun y => (u i).toH1Function.grad y j)) := fun i U hU =>
  (smooth_feedback_h2_projected_source_admissible Q U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (u i) (H i)).2.2.2

theorem Theta_integrable {ι : Type*} (S : Finset ι)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (Q : TriadicCube 2)
    (hQ : Q.scale = m + 129) (u : ι → H10Function (openCubeSet Q)) :
    Integrable (theta'' S M m Q 134 u) (Cutoff.cutoffSampleLaw M).toMeasure := by
  unfold theta''
  refine integrable_finsetSum _ (fun i _ => ?_)
  unfold oldSignedCellAverage
  refine (integrable_finsetSum _ (fun U _ => ?_)).const_mul _
  refine directional_gamma_integrable M h hM hγ (m + 1)
    (fun l hl => hpast l (by omega)) m (by omega) U.val ?_ _
  have := scale_eq_sub_of_mem_descendantsAtDepth U.property
  rw [this, hQ]
  push_cast
  ring

/-- The consumer hypotheses on the actual OLD objects. -/
theorem actual_consumer_hyp {ι : Type*} (S : Finset ι)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (Q : TriadicCube 2) (hQ : Q = originCube 2 (m + 129))
    (u : ι → H10Function (openCubeSet Q))
    (H : ∀ i, HasWeakHessianOn (openCubeSet Q) (u i).toH1Function)
    (Z : Cutoff.CutoffSample 2 → ι → Vec 2 → BlockVec 2)
    (hZ : ∀ ω i, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) (fun x => (u i).toH1Function.grad x) (Z ω i))
    {v : ℝ} (hv : 0 ≤ v)
    (hOm : omega2 S Q u ≤ (1 / 2) * v)
    (hds : deltaSq' S Q 134 u ≤ lambda8DeltaN ^ 2 * v) :
    ConsumerHyp (Cutoff.cutoffSampleLaw M).toMeasure
      (gap' S M m Q 134 u Z) (apair S M m Q 134 u) (pK' S M m Q 134 u)
      (pD S M m Q 134 u) (rK' S M m Q 134 u)
      (rD S M m Q 134 u (hcenter'' Q u H 134))
      (fun ω => bhist M m Q 134 ω)
      (fun ω => max (bhist M m Q 134 ω - 14103 / 10000) 0)
      (theta'' S M m Q 134 u) (elift S M m Q 134 u)
      v (1 / 2) lambda8DeltaN mainSourceMeanPrefix (xi'' M h m) (mStar' M)
      (14103 / 10000) (5 / 10 ^ 24) (omega2 S Q u) (deltaSq' S Q 134 u) (76 / 100) := by
  classical
  have hQs : Q.scale = m + 129 := by subst hQ; rfl
  have hpast' : ∀ n < m + 1, nativeInductionState M h n := fun n hn => hpast n (by omega)
  have hbank := bank_B M h hM hγ m (fun n hn => hpast n hn.le) Q hQs
  have hcenter := hcenter'' Q u H 134
  have hcap : ∀ U : TriadicCube 2, U ∈ descendantsAtDepth Q 134 →
      (∫ ω, smoothFeedbackCellT M m U ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainSourceMeanPrefix := by
    intro U hU
    refine smooth_feedback_cell_trace_mean_le_a5 M h hM hγ (m + 1) hpast' m (by omega) U ?_
    have := scale_eq_sub_of_mem_descendantsAtDepth hU
    rw [this, hQs]
    push_cast
    ring
  have hch := smooth_feedback_annealed_cell_charges S M m Q 134
    (fun i x => (u i).toH1Function.grad x) hcap
  have hgam : (∫ ω, theta'' S M m Q 134 u ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      (xi'' M h m / 2) * ∑ i ∈ S, oldSignedCellAverage Q 134
        (fun U => vecNormSq (cellMean Q u i U.val)) := by
    subst hQ
    exact smooth_feedback_annealed_gamma M h hM hγ (m + 1) hpast' m (by omega) S
      (fun i x => (u i).toH1Function.grad x)
  have hW := Wmean_le_Omega2 S Q u
  have ha5 : 0 ≤ mainSourceMeanPrefix := by
    have := mainSourceMeanPrefix_gate
    linarith
  have hxi := xi_nonneg M h hγ m
  have hOm0 : 0 ≤ omega2 S Q u :=
    Finset.sum_nonneg fun i _ => by
      unfold volumeAverage
      exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
        (integral_nonneg fun x => by
          simp only [vecNormSq, vecDot]
          exact Finset.sum_nonneg fun j _ => mul_self_nonneg _)
  have hd0 : 0 ≤ deltaSq' S Q 134 u :=
    Finset.sum_nonneg fun i _ => old_signed_cell_average_nonneg Q 134 _
      fun U => vectorPositiveHaarEnergy_nonneg _ _
  have hPK := PK_Lq M h hM hγ m hpast Q hQs S u
  have hRK := RK_Lq M h hM hγ m hpast Q hQs S u H
  have hEh := Elift_Lq M h hM hγ m hpast Q hQs S u H
  have hRD := RD_bounds S M m Q u H hcenter (b := 14103 / 10000) (by norm_num) hbank.1
  have hm0 := mStar_nonneg M
  refine
    { v0 := hv, w0 := by norm_num, dn0 := ?_, a50 := ha5, ξ0 := hxi, m0 := hm0,
      b0 := by norm_num, ε0 := by norm_num, c10 := by norm_num, c11 := by norm_num,
      Om0 := hOm0, Om := hOm, ds0 := hd0, ds := hds, mGap := ?_,
      mPK := PK_measurable S M m Q 134 u, mPD := PD_measurable S M m Q 134 u,
      mRK := RK_measurable S M m Q 134 u, mRD := RD_measurable S M m Q 134 u hcenter,
      mB := Bhist_measurable M m Q,
      mRs := ((Bhist_measurable M m Q).sub_const _).max measurable_const,
      mAp := Apair_measurable S M m Q 134 u, mTh := Theta_measurable S M m Q 134 u,
      mEh := Elift_measurable S M m Q 134 u, nGap := ?_,
      nAp := Apair_nonneg S M m Q 134 u, nPK := PK_nonneg S M m Q 134 u,
      nPD := PD_nonneg S M m Q 134 u, nRK := RK_nonneg S M m Q 134 u,
      nRD := RD_nonneg S M m Q 134 u hcenter, nB := Bhist_nonneg M m Q 134,
      nRs := fun ω => le_max_right _ _, nTh := Theta_nonneg S M m Q 134 u,
      nEh := Elift_nonneg S M m Q 134 u, p1 := ?_, p2 := ?_,
      p4 := fun ω => by
        have := le_max_left (bhist M m Q 134 ω - 14103 / 10000) 0
        linarith [le_max_left (bhist M m Q 134 ω - 14103 / 10000) 0],
      iAp := Apair_integrable S M m Q 134 u, iPK := hPK.1,
      iPD := PD_integrable M h hM hγ m hpast Q hQs S u, iRK := hRK.1,
      iRD := hRD.1, iTh := Theta_integrable S M h hM hγ m hpast Q hQs u,
      eAp := ?_, ePK := ?_, ePD := ?_, eRK := hRK.2.1, eRD := hRD.2,
      eTh := ?_, qB := hbank.1, qRs := hbank.2, qPK := hPK.2, qRK := hRK.2.2, qEh := hEh }
  · unfold lambda8DeltaN lambda8Rho
    positivity
  · exact smooth_feedback_h2_gap_measurable S M m Q 134 u Z hZ
  · intro ω
    exact Finset.sum_nonneg fun i _ =>
      smooth_feedback_scalar_field_energy_nonneg Q M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar M m).property _ _
  · intro ω
    exact actual_gap_le_gpair S M m Q 134 u H
      (fun i U hU => (smooth_feedback_h2_projected_source_admissible Q U
        (openCubeSet_subset_of_mem_descendantsAtDepth hU) (u i) (H i)).2.1)
      hcenter Z (fun ω i => hZ ω i) ω
  · intro ω
    exact actual_gap_le_two S M m Q 134 u H Z hZ ω
  · exact hch.1.trans (mul_le_mul_of_nonneg_left hW (by positivity))
  · exact hch.2.1.trans (mul_le_mul_of_nonneg_left hW (by positivity))
  · exact hch.2.2.trans (mul_le_mul_of_nonneg_left hW (by positivity))
  · exact hgam.trans (mul_le_mul_of_nonneg_left hW (by positivity))

end

end ASDExplicitGamma.Scalar

