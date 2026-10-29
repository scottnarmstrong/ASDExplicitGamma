module

public import ASDExplicitGamma.Native.HeatStepRows2
public import ASDExplicitGamma.Native.HeatVHEATThetaFixedEps
public import ASDExplicitGamma.Statements.Theta

/-! Theta-normalized pass row of the `ns`-shell refined heat step.  With `τ = θ = γ/γ₀` and the
moment curves normalized by `τ^j`, the same configured row holds as at the endpoint, given the
`τ`-scaled caps `X ≤ τ x`, `avg ≤ τ y`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Set Homogenization Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native ProbabilityTheory
open scoped ENNReal Topology

theorem theta_pos_le_one (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) :
    0 < theta M ∧ theta M ≤ 1 := by
  have h0 := M.shellPrefix.gamma_pos
  have hz : (0 : ℝ) < gammaZero := by norm_num [gammaZero]
  exact ⟨div_pos h0 hz, (div_le_one hz).2 hg⟩

section ThetaRow

variable (ns : ℕ) [NeZero ns] (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)

/-- The theta-normalized curves `m_j / θ^j`. -/
noncomputable def nativeHeatStepCurveN (j : ℕ) (t : ℝ) : ℝ :=
  nativeHeatStepCurve ns M h hM m j t / theta M ^ j

noncomputable def nativeHeatStepCurveDerivN (j : ℕ) (t : ℝ) : ℝ :=
  nativeHeatStepCurveDeriv ns M h hM m j t / theta M ^ j

/-- The drift coefficient is `θ`-proportional: `e ≤ θ old.e` and `e c' ≤ θ c`. -/
theorem nativeHeatStep_driftTheta (hgen : NativeHeatGenNum ns) (hg : M.gamma ≤ gammaZero) :
    (0 ≤ (heatVHEATDriftEGen ns) M ∧
      (heatVHEATDriftEGen ns) M ≤ theta M * ((nativeHeatOldRowGen ns).e : ℝ)) ∧
    (heatVHEATDriftEGen ns) M * (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
        (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) ≤ theta M * (nativeHeatExpArgGen ns : ℝ) := by
  have hg0 := M.shellPrefix.gamma_pos
  obtain ⟨hθ0, hθ1⟩ := theta_pos_le_one M hg
  have hz : (0 : ℝ) < gammaZero := by norm_num [gammaZero]
  have he0 : 0 ≤ (heatVHEATDriftEGen ns) M := by
    unfold heatVHEATDriftEGen
    positivity
  have hE0 := hgen.efactor gammaZero hz.le le_rfl
  have hec : (heatVHEATDriftEGen ns) M ≤ theta M * ((9 / 2 : ℝ) * gammaZero *
      (3 : ℝ) ^ (2 * gammaZero * (ns : ℝ))) := by
    unfold heatVHEATDriftEGen
    have hγ : M.gamma = theta M * gammaZero := by
      unfold theta; field_simp
    have hp : (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ)) ≤ (3 : ℝ) ^ (2 * gammaZero * (ns : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have : (0 : ℝ) ≤ (ns : ℝ) := Nat.cast_nonneg _
      nlinarith
    calc (9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * M.gamma * (ns : ℝ))
        ≤ (9 / 2 : ℝ) * M.gamma * (3 : ℝ) ^ (2 * gammaZero * (ns : ℝ)) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by rw [hγ]; ring
  have heold : (heatVHEATDriftEGen ns) M ≤ theta M * ((nativeHeatOldRowGen ns).e : ℝ) :=
    hec.trans (mul_le_mul_of_nonneg_left hE0 hθ0.le)
  refine ⟨⟨he0, heold⟩, ?_⟩
  have hB : (3683 / 2500 : ℝ) ≤ (nativeHeatB : ℝ) := by
    have : (3683 / 2500 : ℚ) ≤ nativeHeatB := by
      norm_num [nativeHeatB, nativeHeatRQ, nativeE, nativeGamma, nativeB]
    calc (3683 / 2500 : ℝ) = ((3683 / 2500 : ℚ) : ℝ) := by norm_num
      _ ≤ (nativeHeatB : ℝ) := Rat.cast_le.mpr this
  have hK : 0 ≤ (nativeHeatK : ℝ) := by norm_num [nativeHeatK]
  have hMm : 0 ≤ (nativeHeatM : ℝ) := by norm_num [nativeHeatM]
  have hpoly : 2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) + (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2 ≤
      2 * (nativeHeatK : ℝ) * (nativeHeatB : ℝ) + (nativeHeatM : ℝ) * (nativeHeatB : ℝ) ^ 2 := by
    have h1 : (3683 / 2500 : ℝ) ^ 2 ≤ (nativeHeatB : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hB 2
    nlinarith [mul_le_mul_of_nonneg_left hB hK, mul_le_mul_of_nonneg_left h1 hMm]
  have hpoly0 : 0 ≤ 2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
      (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2 := by positivity
  have hcast : (nativeHeatExpArgGen ns : ℝ) = ((nativeHeatOldRowGen ns).e : ℝ) *
      (2 * (nativeHeatK : ℝ) * (nativeHeatB : ℝ) + (nativeHeatM : ℝ) * (nativeHeatB : ℝ) ^ 2) := by
    unfold nativeHeatExpArgGen nativeHeatExpArg
    push_cast
    ring
  rw [hcast]
  have hold0 : 0 ≤ ((nativeHeatOldRowGen ns).e : ℝ) := he0.trans (by
    have := hE0; have h2 : (heatVHEATDriftEGen ns) M ≤ theta M * ((nativeHeatOldRowGen ns).e : ℝ) := heold
    nlinarith)
  calc (heatVHEATDriftEGen ns) M * (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
        (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2)
      ≤ (theta M * ((nativeHeatOldRowGen ns).e : ℝ)) *
        (2 * (nativeHeatK : ℝ) * (nativeHeatB : ℝ) + (nativeHeatM : ℝ) * (nativeHeatB : ℝ) ^ 2) :=
        mul_le_mul heold hpoly hpoly0 (by positivity)
    _ = _ := by ring


/-- Theta-normalized pass row: given `X ≤ θ x`, the `20`-moment cap `(θ y)^20` and the raw cap
`F`, the normalized curves satisfy the endpoint configured row. -/
theorem nativeHeatStep_rowTheta (hns9 : 9 ≤ ns) (hns160 : ns ≤ 160)
    (hnum : NativeHeatStepPassNum ns) (hgen : NativeHeatGenNum ns)
    (hg : M.gamma ≤ gammaZero)
    (hpast : ∀ l < m + 1, nativeInductionState M h l)
    (hstate : nativeInductionState M h (m + 1))
    (hX : ∀ t ∈ Ioo (0 : ℝ) 1,
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatStepAux ns M h hM m t)).toReal ≤ theta M * ((nativeHeatFramesGen ns).x : ℝ))
    (hF : ∀ t ∈ Ioo (0 : ℝ) 1,
      heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
            (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
            (nativeHeatTheta : ℝ) t)) ≤ ((nativeHeatFramesGen ns).raw : ℝ))
    (y : ℚ) (hy : 0 ≤ y)
    (hcapY : ∀ t ∈ Ioo (0 : ℝ) 1,
      nativeHeatStepMoment ns M h hM m 20 t ≤ (theta M * (y : ℝ)) ^ 20) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ j ≤ 20,
      nativeHeatStepCurveDerivN ns M h hM m j s ≤
        (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) * nativeHeatStepCurveN ns M h hM m j s +
        4 * (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) *
          nativeHeatStepCurveN ns M h hM m (j - 1) s +
        (if j = 0 then 0 else
          (nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
            (nativeHeatFixedGen ns) y j : ℝ)) := by
  classical
  have hns1331 : ns ≤ 1331 := by omega
  obtain ⟨hθ0, hθ1⟩ := theta_pos_le_one M hg
  have hy0 : (0 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hθy : 0 ≤ theta M * (y : ℝ) := mul_nonneg hθ0.le hy0
  have hcaps : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 →
      ((heatVHEATDriftRefinedPhysicalXExtendedGen ns) M m t
        (nativeHeatQ3RefinedCarrierSourceAuxCenterGaussianGen M m ns
          (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
          (nativeHeatTheta : ℝ) t)).toReal ≤ theta M * ((nativeHeatFramesGen ns).x : ℝ) ∧
      (nativeHeatQ3RefinedCarrierSourceAverageNormGen ns) M h hM m
        (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
        (nativeHeatTheta : ℝ) t ≤ theta M * (y : ℝ) ∧
      heatRefinedRawEnvelope ns
        (heatVHEATDriftAuxVariance Finset.univ
          (nativeHeatQ3RefinedCarrierSourceAuxCenterVarianceGen M m ns
            (nativeHeatQ3RefinedCarrierFreshShellFamilyChosenGen M h hM m ns)
            (nativeHeatTheta : ℝ) t)) ≤ ((nativeHeatFramesGen ns).raw : ℝ) := by
    intro t ht
    exact ⟨hX t ht, nativeHeatStep_avgNorm_le_of_moment_le ns M h hM m hns1331 hg hpast t ht
      _ hθy (hcapY t ht), hF t ht⟩
  have hv := nativeHeatVHEATBackwardInequality_source_gen ns hns9 (by omega) M h hM hg m
    hpast hstate (theta M * ((nativeHeatFramesGen ns).x : ℝ)) (theta M * (y : ℝ))
    ((nativeHeatFramesGen ns).raw : ℝ) hcaps
  obtain ⟨⟨he0, heold⟩, hdrift⟩ := nativeHeatStep_driftTheta ns M hgen hg
  have hx0 : (0 : ℝ) < ((nativeHeatFramesGen ns).x : ℝ) := by exact_mod_cast hnum.x_pos
  have hraw0 : (0 : ℝ) ≤ ((nativeHeatFramesGen ns).raw : ℝ) := by exact_mod_cast hnum.raw_nonneg
  have hold0 : (0 : ℝ) ≤ ((nativeHeatOldRowGen ns).e : ℝ) := by exact_mod_cast hnum.old_e_nonneg
  intro s hs j hj
  by_cases hj0 : j = 0
  · subst j
    have e1 : nativeHeatStepCurveDerivN ns M h hM m 0 s = 0 := by
      simp [nativeHeatStepCurveDerivN, nativeHeatStepCurveDeriv]
    simp [e1]
  · have hj1 : 1 ≤ j := by omega
    have hjR : (0 : ℝ) ≤ (j : ℝ) := by positivity
    have hτj : 0 < theta M ^ j := pow_pos hθ0 j
    have hopen : ∀ t ∈ Ioo (0 : ℝ) 1,
        nativeHeatStepCurveDerivN ns M h hM m j t ≤
          (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) * nativeHeatStepCurveN ns M h hM m j t +
          4 * (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) *
            nativeHeatStepCurveN ns M h hM m (j - 1) t +
          (nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
            (nativeHeatFixedGen ns) y j : ℝ) := by
      intro t ht
      obtain ⟨hder, hineq⟩ := hv j hj1 hj t ht
      rw [hder.deriv] at hineq
      -- error term
      have hE1 := nativeHeatVHEATErrorEk_mono_drift_remainder j 20
        ((heatVHEATDriftEGen ns) M) (theta M * ((nativeHeatOldRowGen ns).e : ℝ))
        (nativeHeatK : ℝ) (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatM : ℝ)
        (nativeHeatSB : ℝ) (nativeHeatSB : ℝ) (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ)
        (theta M * ((nativeHeatFramesGen ns).x : ℝ)) (theta M * (y : ℝ)) (3 / 10 ^ 46 : ℝ)
        ((nativeHeatFramesGen ns).raw : ℝ) he0 heold (by norm_num [nativeHeatK]) le_rfl
        (by norm_num [nativeHeatM]) le_rfl (by norm_num [nativeHeatSB]) le_rfl
        (by norm_num [nativeHeatTheta]) (by norm_num) (mul_pos hθ0 hx0) hθy (by positivity) hraw0
      have hE2 := nativeHeatVHEATErrorEk_fixedEps_scaled_le (theta M)
        ((nativeHeatOldRowGen ns).e : ℝ) (nativeHeatK : ℝ) (nativeHeatM : ℝ)
        (nativeHeatSB : ℝ) (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ)
        ((nativeHeatFramesGen ns).x : ℝ) (y : ℝ) (3 / 10 ^ 46 : ℝ)
        ((nativeHeatFramesGen ns).raw : ℝ) j hθ0 hθ1 hold0 (by norm_num [nativeHeatK])
        (by norm_num [nativeHeatM]) (by norm_num [nativeHeatSB]) (by norm_num [nativeHeatTheta])
        (by norm_num) hx0 hy0 (by positivity) hraw0 hj1 hj
      have hE3 := nativeHeatStep_vheatError_le_forcingAt ns hnum j hj1 hj
        ((nativeHeatOldRowGen ns).e : ℝ) hold0 le_rfl y hy
      have hEk : nativeHeatVHEATErrorEk j 20 ((heatVHEATDriftEGen ns) M)
          (nativeHeatK : ℝ) (nativeHeatM : ℝ) (nativeHeatSB : ℝ) (nativeHeatTheta : ℝ)
          (3683 / 2500 : ℝ) (theta M * ((nativeHeatFramesGen ns).x : ℝ)) (theta M * (y : ℝ))
          (3 / 10 ^ 46 : ℝ) ((nativeHeatFramesGen ns).raw : ℝ) ≤
          theta M ^ j * (nativeHeatForcingAt (nativeHeatOldRowGen ns)
            (nativeHeatFramesGen ns) (nativeHeatFixedGen ns) y j : ℝ) :=
        hE1.trans (hE2.trans (mul_le_mul_of_nonneg_left hE3 (pow_nonneg hθ0.le j)))
      have hmj := nativeHeatStep_moment_nonneg ns M h hM m hns1331 hg hpast t ht j hj1 hj
      have hmj1 : 0 ≤ nativeHeatStepMoment ns M h hM m (j - 1) t := by
        by_cases hjm : j - 1 = 0
        · rw [hjm, nativeHeatStep_moment_zero]; norm_num
        · exact nativeHeatStep_moment_nonneg ns M h hM m hns1331 hg hpast t ht (j - 1)
            (by omega) (by omega)
      have hlow : nativeHeatStepCurve ns M h hM m (j - 1) t =
          nativeHeatStepMoment ns M h hM m (j - 1) t := by
        by_cases hjm : j - 1 = 0
        · rw [hjm, nativeHeatStep_moment_zero]; simp [nativeHeatStepCurve]
        · rw [nativeHeatStep_curve_eq_moment ns M h hM m (j - 1) hjm]
      have hcur : nativeHeatStepCurve ns M h hM m j t = nativeHeatStepMoment ns M h hM m j t :=
        by rw [nativeHeatStep_curve_eq_moment ns M h hM m j hj0]
      have hgenEq : nativeHeatStepCurveDeriv ns M h hM m j t =
          nativeHeatStepGenerator ns M h hM m j t := by
        rw [nativeHeatStep_curveDeriv_eq_generator ns M h hM m j hj0]
      change nativeHeatStepGenerator ns M h hM m j t ≤
        (j : ℝ) * (heatVHEATDriftEGen ns) M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
          (nativeHeatStepMoment ns M h hM m j t +
            4 * nativeHeatStepMoment ns M h hM m (j - 1) t) +
        nativeHeatVHEATErrorEk j 20 ((heatVHEATDriftEGen ns) M) (nativeHeatK : ℝ)
          (nativeHeatM : ℝ) (nativeHeatSB : ℝ) (nativeHeatTheta : ℝ) (3683 / 2500 : ℝ)
          (theta M * ((nativeHeatFramesGen ns).x : ℝ)) (theta M * (y : ℝ)) (3 / 10 ^ 46 : ℝ)
          ((nativeHeatFramesGen ns).raw : ℝ) at hineq
      -- the drift part
      have hcoef : (j : ℝ) * ((heatVHEATDriftEGen ns) M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2)) ≤
          (j : ℝ) * (theta M * (nativeHeatExpArgGen ns : ℝ)) :=
        mul_le_mul_of_nonneg_left hdrift hjR
      have hsum0 : 0 ≤ nativeHeatStepMoment ns M h hM m j t +
          4 * nativeHeatStepMoment ns M h hM m (j - 1) t := by positivity
      have hdr : (j : ℝ) * (heatVHEATDriftEGen ns) M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2) *
          (nativeHeatStepMoment ns M h hM m j t +
            4 * nativeHeatStepMoment ns M h hM m (j - 1) t) ≤
          (j : ℝ) * (theta M * (nativeHeatExpArgGen ns : ℝ)) *
          (nativeHeatStepMoment ns M h hM m j t +
            4 * nativeHeatStepMoment ns M h hM m (j - 1) t) := by
        have := mul_le_mul_of_nonneg_right hcoef hsum0
        calc _ = (j : ℝ) * ((heatVHEATDriftEGen ns) M *
          (2 * (nativeHeatK : ℝ) * (3683 / 2500 : ℝ) +
            (nativeHeatM : ℝ) * (3683 / 2500 : ℝ) ^ 2)) *
          (nativeHeatStepMoment ns M h hM m j t +
            4 * nativeHeatStepMoment ns M h hM m (j - 1) t) := by ring
          _ ≤ _ := this
      have hbig : nativeHeatStepGenerator ns M h hM m j t ≤
          (j : ℝ) * (theta M * (nativeHeatExpArgGen ns : ℝ)) *
          (nativeHeatStepMoment ns M h hM m j t +
            4 * nativeHeatStepMoment ns M h hM m (j - 1) t) +
          theta M ^ j * (nativeHeatForcingAt (nativeHeatOldRowGen ns)
            (nativeHeatFramesGen ns) (nativeHeatFixedGen ns) y j : ℝ) := by
        linarith
      -- normalize
      unfold nativeHeatStepCurveDerivN nativeHeatStepCurveN
      rw [hgenEq, hcur, hlow]
      have hpj : theta M ^ j = theta M * theta M ^ (j - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hc0 : 0 ≤ (nativeHeatExpArgGen ns : ℝ) := by exact_mod_cast hnum.c_nonneg
      set N := nativeHeatStepMoment ns M h hM m j t
      set N1 := nativeHeatStepMoment ns M h hM m (j - 1) t
      set c := (nativeHeatExpArgGen ns : ℝ)
      set F := (nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
            (nativeHeatFixedGen ns) y j : ℝ)
      set τ := theta M
      rw [div_le_iff₀ hτj]
      have e1 : N / τ ^ j * τ ^ j = N := by field_simp
      have e2 : N1 / τ ^ (j - 1) * τ ^ j = N1 * τ := by
        rw [hpj]; field_simp
      have hrhs : (c * j * (N / τ ^ j) + 4 * c * j * (N1 / τ ^ (j - 1)) + F) * τ ^ j =
          c * j * N + 4 * c * j * (N1 * τ) + F * τ ^ j := by
        calc _ = c * j * (N / τ ^ j * τ ^ j) + 4 * c * j * (N1 / τ ^ (j - 1) * τ ^ j)
              + F * τ ^ j := by ring
          _ = _ := by rw [e1, e2]
      rw [hrhs]
      have hjc : 0 ≤ c * j := mul_nonneg hc0 hjR
      have a1 : τ * (c * j * N) ≤ c * j * N :=
        mul_le_of_le_one_left (mul_nonneg hjc hmj) hθ1
      have a2 : τ * (c * j * N1) ≤ c * j * N1 :=
        mul_le_of_le_one_left (mul_nonneg hjc hmj1) hθ1
      nlinarith [hbig, a1, a2]
    have hcontL : ContinuousOn (nativeHeatStepCurveDerivN ns M h hM m j) (Icc (0 : ℝ) 1) := by
      unfold nativeHeatStepCurveDerivN
      exact (nativeHeatStep_curveDeriv_contOn ns M h hM m j hj).div_const _
    have hcontR : ContinuousOn (fun t =>
        (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) * nativeHeatStepCurveN ns M h hM m j t +
          4 * (nativeHeatExpArgGen ns : ℝ) * (j : ℝ) *
            nativeHeatStepCurveN ns M h hM m (j - 1) t +
          (nativeHeatForcingAt (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
            (nativeHeatFixedGen ns) y j : ℝ)) (Icc (0 : ℝ) 1) := by
      have h1 := (nativeHeatStep_curve_contOn ns M h hM m j hj).div_const (theta M ^ j)
      have h2 := (nativeHeatStep_curve_contOn ns M h hM m (j - 1) (by omega)).div_const
        (theta M ^ (j - 1))
      unfold nativeHeatStepCurveN
      exact ((continuousOn_const.mul h1).add (continuousOn_const.mul h2)).add continuousOn_const
    rw [if_neg hj0]
    exact nativeHeatStep_le_on_Icc_of_Ioo hcontL hcontR hopen s hs

end ThetaRow

end ASDExplicitGamma.Native
