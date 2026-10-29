module

public import ASDExplicitGamma.Inverse.GoodCellDerivative
public import ASDExplicitGamma.Gaussian.SupMeanDyadicConvergence
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! The good-cell first-jet gate controls the oscillation of actual later-band
averages, uniformly over all contained response cubes. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Model

noncomputable section

private theorem later_band_derivative_bound
    (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (B : ℝ)
    (hB : 0 ≤ B)
    (hBpoint : ∀ x ∈ supMeanClosedSquare (cubeCenter Q) (cubeScaleFactor Q),
      ‖laterBandTensor Q3SpatialJet.first n J weights ω x‖ ≤ B)
    (x : Vec 2) (hx : x ∈ supMeanClosedSquare (cubeCenter Q) (cubeScaleFactor Q)) :
    ‖fderiv ℝ (laterScalarBand n J weights ω) x‖ ≤ B := by
  classical
  let a : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 (fun i => laterScalarFirst n J weights ω i x)
  have htensor := hBpoint x hx
  rw [later_band_first_tensor_eq] at htensor
  have ha : ‖a‖ ≤ B / Real.sqrt 2 := by
    have htensor' : Real.sqrt 2 * ‖a‖ ≤ B := by
      calc
        Real.sqrt 2 * ‖a‖ = ‖Real.sqrt 2 • a‖ := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2))]
        _ ≤ B := htensor
    apply (le_div_iff₀ (Real.sqrt_pos.2 (by norm_num))).2
    simpa only [mul_comm] using htensor'
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro v
  have hv (i : Fin 2) : |v i| ≤ ‖v‖ := by
    have hh := (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mp
      (le_rfl : ‖v‖ ≤ ‖v‖) i
    simpa only [Real.norm_eq_abs] using hh
  have hderiv (i : Fin 2) :
      (fderiv ℝ (laterScalarBand n J weights ω) x) (basisVec i) =
        laterScalarFirst n J weights ω i x := by
    simpa only [smoothScalarDerivative] using
      congrFun (later_scalar_band_derivative n J weights ω i) x
  have hrepr :
      (fderiv ℝ (laterScalarBand n J weights ω) x) v =
        ∑ i : Fin 2, v i * laterScalarFirst n J weights ω i x := by
    have hvbasis : v = ∑ i : Fin 2, v i • basisVec i := by
      ext i
      fin_cases i <;> simp [Fin.sum_univ_two, basisVec]
    calc
      _ = (fderiv ℝ (laterScalarBand n J weights ω) x)
          (∑ i : Fin 2, v i • basisVec i) := congrArg _ hvbasis
      _ = ∑ i : Fin 2,
          (fderiv ℝ (laterScalarBand n J weights ω) x) (v i • basisVec i) := map_sum _ _ _
      _ = ∑ i : Fin 2, v i * laterScalarFirst n J weights ω i x := by
        simp [hderiv, smul_eq_mul]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 2))
    (fun i => |laterScalarFirst n J weights ω i x|) (fun i => |v i|)
  have hgradSq : (∑ i : Fin 2, |laterScalarFirst n J weights ω i x| ^ 2) ≤
      (B / Real.sqrt 2) ^ 2 := by
    have hnormsq : ‖a‖ ^ 2 =
        ∑ i : Fin 2, |laterScalarFirst n J weights ω i x| ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [a, sq_abs]
    rw [← hnormsq]
    exact (sq_le_sq₀ (norm_nonneg _) (div_nonneg hB (Real.sqrt_nonneg _))).2 ha
  have hcs' :
      (∑ i : Fin 2, |laterScalarFirst n J weights ω i x| * |v i|) ^ 2 ≤
        (∑ i : Fin 2, |laterScalarFirst n J weights ω i x| ^ 2) *
          ∑ i : Fin 2, |v i| ^ 2 := by
    simpa using hcs
  have hvSq : (∑ i : Fin 2, |v i| ^ 2) ≤ 2 * ‖v‖ ^ 2 := by
    calc
      _ ≤ ∑ i : Fin 2, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact sq_le_sq₀ (abs_nonneg _) (norm_nonneg _) |>.2 (hv i)
      _ = 2 * ‖v‖ ^ 2 := by simp
  have hsumAbs :
      |∑ i : Fin 2, v i * laterScalarFirst n J weights ω i x| ≤
        ∑ i : Fin 2, |v i| * |laterScalarFirst n J weights ω i x| := by
    calc
      _ ≤ ∑ i : Fin 2, |v i * laterScalarFirst n J weights ω i x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul]
  have hsumBound :
      ∑ i : Fin 2, |laterScalarFirst n J weights ω i x| * |v i| ≤
        B * ‖v‖ := by
    have hsq :
        (∑ i : Fin 2, |laterScalarFirst n J weights ω i x| * |v i|) ^ 2 ≤
          (B * ‖v‖) ^ 2 := by
      calc
        _ ≤ (∑ i : Fin 2, |laterScalarFirst n J weights ω i x| ^ 2) *
            ∑ i : Fin 2, |v i| ^ 2 := hcs'
        _ ≤ (B / Real.sqrt 2) ^ 2 * (2 * ‖v‖ ^ 2) :=
          mul_le_mul hgradSq hvSq (by positivity) (by positivity)
        _ = (B * ‖v‖) ^ 2 := by
          rw [div_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))]
          ring
    exact (sq_le_sq₀ (by positivity) (mul_nonneg hB (norm_nonneg _))).mp hsq
  calc
    ‖(fderiv ℝ (laterScalarBand n J weights ω) x) v‖
        = |∑ i : Fin 2, v i * laterScalarFirst n J weights ω i x| := by
          rw [hrepr, Real.norm_eq_abs]
    _ ≤ B * ‖v‖ := hsumAbs.trans (by simpa only [mul_comm] using hsumBound)

private theorem cube_average_deviation_le
    (S : TriadicCube 2) (f : Vec 2 → ℝ) (c C : ℝ)
    (hf : MemLp f 2 (normalizedCubeMeasure S))
    (hpoint : ∀ x ∈ cubeSet S, |f x - c| ≤ C) :
    |cubeAverage S f - c| ≤ C := by
  have hsub := cubeAverage_sub_const_of_memLp_two S hf c
  rw [← hsub, cubeAverage_eq_integral_normalizedCubeMeasure]
  have hfint : Integrable f (normalizedCubeMeasure S) := hf.integrable (by norm_num)
  have hcint : Integrable (fun _ : Vec 2 => c) (normalizedCubeMeasure S) := integrable_const c
  have hdiffint : Integrable (fun x => f x - c) (normalizedCubeMeasure S) := by
    convert hfint.sub hcint using 1
  have habsint : Integrable (fun x => |f x - c|) (normalizedCubeMeasure S) := by
    simpa only [Real.norm_eq_abs] using hdiffint.norm
  have hpointAE : ∀ᵐ x ∂normalizedCubeMeasure S, |f x - c| ≤ C :=
    (normalized_cube_support S).mono (fun x hx => hpoint x hx)
  calc
    |∫ x, (f x - c) ∂normalizedCubeMeasure S| ≤
        ∫ x, |f x - c| ∂normalizedCubeMeasure S := abs_integral_le_integral_abs
    _ ≤ ∫ _x, C ∂normalizedCubeMeasure S :=
      integral_mono_ae habsint (integrable_const C) hpointAE
    _ = C := by simp [Measure.real_def, normalizedCubeMeasure_apply_univ]

/-- On a good source cell, every descendant cube has its actual later-wave
mean within `10 η` of the root mean after division by the root frame. -/
theorem good_cell_later_band_cube_average_oscillation
    (M : ABKModel 2) (Q R : TriadicCube 2) (d : ℕ) (hR : R ∈ descendantsAtDepth Q d)
    (τ η : ℝ) (hη : 0 ≤ η) (ω : Cutoff.CutoffSample 2)
    (hgood : ω ∉ cellFailure M τ η Q) (J : ℤ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale + 40) J, 0 ≤ weights k ∧ weights k ≤ 1) :
    |cubeAverage R ((laterBandW2 Q (Q.scale + 40) J weights ω).restrict hR).value.toFun /
        (Annealed.sigmaBar M (Q.scale + 40) : ℝ) -
      cubeAverage Q (laterBandW2 Q (Q.scale + 40) J weights ω).value.toFun /
        (Annealed.sigmaBar M (Q.scale + 40) : ℝ)| ≤ 10 * η := by
  classical
  let n := Q.scale + 40
  let σ := (Annealed.sigmaBar M n : ℝ)
  let f := laterScalarBand n J weights ω
  let B := ∑ k ∈ Finset.Ioc n J, |weights k| *
    ‖supMeanShellSquareTensor Q3SpatialJet.first (cubeCenter Q)
      (cubeScaleFactor Q) (ω.val k)‖
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M n).1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hgate :
      ∑ k ∈ Finset.Ioc n J, |weights k| *
        waveGateDerivativeSize (cubeCenter Q) (cubeScaleFactor Q) σ (ω.val k) ≤ 10 * η := by
    calc
      _ ≤ ∑ k ∈ Finset.Ioc n J, η *
          (3:ℝ)^(-((k - n : ℤ) : ℝ) / 8) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_Ioc.mp hk
        have hweight := hw k hk
        have hder := good_cell_wave_gate M Q τ η ω hgood k hk'.1
        have hnonneg : 0 ≤ waveGateDerivativeSize (cubeCenter Q)
            (cubeScaleFactor Q) σ (ω.val k) := by
          unfold waveGateDerivativeSize
          exact add_nonneg
            (mul_nonneg (div_nonneg (Homogenization.cubeScaleFactor_pos' Q).le hσ.le)
              (norm_nonneg _))
            (mul_nonneg (div_nonneg (sq_nonneg _) hσ.le) (norm_nonneg _))
        have hweighted : |weights k| *
            waveGateDerivativeSize (cubeCenter Q) (cubeScaleFactor Q) σ
              (ω.val k) ≤ waveGateDerivativeSize (cubeCenter Q)
                (cubeScaleFactor Q) σ (ω.val k) := by
          rw [abs_of_nonneg hweight.1]
          exact mul_le_of_le_one_left hnonneg hweight.2
        exact hweighted.trans hder
      _ = η * ∑ k ∈ Finset.Ioc n J,
          (3:ℝ)^(-((k - n : ℤ) : ℝ) / 8) := by rw [Finset.mul_sum]
      _ ≤ η * 10 := mul_le_mul_of_nonneg_left
        (wave_gate_interval_threshold_sum_le_ten n J) hη
      _ = 10 * η := by ring
  have hBtoGate : B * cubeScaleFactor Q ≤ σ *
      (∑ k ∈ Finset.Ioc n J, |weights k| *
        waveGateDerivativeSize (cubeCenter Q) (cubeScaleFactor Q) σ (ω.val k)) := by
    dsimp only [B]
    calc
      _ = ∑ k ∈ Finset.Ioc n J,
          |weights k| * ‖supMeanShellSquareTensor Q3SpatialJet.first
            (cubeCenter Q) (cubeScaleFactor Q) (ω.val k)‖ * cubeScaleFactor Q :=
        Finset.sum_mul _ _ _
      _ ≤ ∑ k ∈ Finset.Ioc n J, σ * (|weights k| *
          waveGateDerivativeSize (cubeCenter Q) (cubeScaleFactor Q) σ (ω.val k)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hfirst : (cubeScaleFactor Q / σ) *
            ‖supMeanShellSquareTensor Q3SpatialJet.first (cubeCenter Q)
              (cubeScaleFactor Q) (ω.val k)‖ ≤
            waveGateDerivativeSize (cubeCenter Q) (cubeScaleFactor Q) σ
              (ω.val k) := by
          unfold waveGateDerivativeSize
          exact le_add_of_nonneg_right
            (mul_nonneg (div_nonneg (sq_nonneg _) hσ.le) (norm_nonneg _))
        calc
          |weights k| *
              ‖supMeanShellSquareTensor Q3SpatialJet.first (cubeCenter Q)
                (cubeScaleFactor Q) (ω.val k)‖ * cubeScaleFactor Q =
              σ * (|weights k| * ((cubeScaleFactor Q / σ) *
                ‖supMeanShellSquareTensor Q3SpatialJet.first (cubeCenter Q)
                  (cubeScaleFactor Q) (ω.val k)‖)) := by
                    field_simp [hσ.ne']
          _ ≤ σ * (|weights k| * waveGateDerivativeSize
              (cubeCenter Q) (cubeScaleFactor Q) σ (ω.val k)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hfirst (abs_nonneg _)) hσ.le
      _ = σ * ∑ k ∈ Finset.Ioc n J, |weights k| *
          waveGateDerivativeSize (cubeCenter Q) (cubeScaleFactor Q) σ (ω.val k) := by
        rw [Finset.mul_sum]
  have hBscaled : B * cubeScaleFactor Q ≤ σ * (10 * η) :=
    hBtoGate.trans (mul_le_mul_of_nonneg_left hgate hσ.le)
  have hpoint (x : Vec 2) (hx : x ∈ cubeSet Q) :
      |f x - f (cubeCenter Q)| ≤ B * cubeScaleFactor Q / 2 := by
    let S := supMeanClosedSquare (cubeCenter Q) (cubeScaleFactor Q)
    have hconv : Convex ℝ S := by
      change Convex ℝ (supMeanClosedSquare (cubeCenter Q) (cubeScaleFactor Q))
      rw [supMean_closed_square_eq_Icc]
      exact convex_Icc _ _
    have hcenter : cubeCenter Q ∈ S :=
      supMean_center_mem_closed_square _ _ (Homogenization.cubeScaleFactor_pos' Q).le
    have hxS : x ∈ S := cube_subset_closed_observation Q hx
    have hder (z : Vec 2) (hz : z ∈ S) :
        HasFDerivWithinAt f (fderiv ℝ f z) S z := by
      have hF := later_scalar_band_hasFDerivAt n J weights ω z
      have heq : fderiv ℝ f z =
          ∑ k ∈ Finset.Ioc n J, weights k • shellScalarDerivative (ω.val k) z := by
        simpa [f] using hF.fderiv
      rw [heq]
      exact hF.hasFDerivWithinAt
    have hnorm (z : Vec 2) (hz : z ∈ S) : ‖fderiv ℝ f z‖ ≤ B :=
      later_band_derivative_bound Q n J weights ω B hB
        (fun y hy => later_band_tensor_norm_le Q3SpatialJet.first n J weights ω
          (cubeCenter Q) (cubeScaleFactor Q) hy) z hz
    have hmv := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      hder hnorm hcenter hxS
    have hdist : ‖x - cubeCenter Q‖ ≤ cubeScaleFactor Q / 2 := by
      apply (pi_norm_le_iff_of_nonneg
        (div_nonneg (Homogenization.cubeScaleFactor_pos' Q).le (by norm_num))).2
      intro i
      have hi := hxS i
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using hi
    have hmv' : |f x - f (cubeCenter Q)| ≤ B * ‖x - cubeCenter Q‖ := by
      simpa only [Real.norm_eq_abs] using hmv
    have habs : |f x - f (cubeCenter Q)| ≤ B * cubeScaleFactor Q / 2 := by
      calc
        _ ≤ B * ‖x - cubeCenter Q‖ := hmv'
        _ ≤ B * (cubeScaleFactor Q / 2) := mul_le_mul_of_nonneg_left hdist hB
        _ = B * cubeScaleFactor Q / 2 := by ring
    exact habs
  have hrootMem : MemLp f 2 (normalizedCubeMeasure Q) := by
    have ht := PlanarW2Infinity.value_memLp_top_normalized
      (laterBandW2 Q n J weights ω)
    have hfour := ht.mono_exponent (by norm_num : (2:ENNReal) ≤ ⊤)
    simpa only [later_band_w2_value, f, n] using hfour
  have hrestr :
      ((laterBandW2 Q n J weights ω).restrict hR).value.toFun =
        (laterBandW2 Q n J weights ω).value.toFun := by
    simp [PlanarW2Infinity.restrict]
  have hRmem : MemLp f 2 (normalizedCubeMeasure R) := by
    have ht := PlanarW2Infinity.value_memLp_top_normalized
      ((laterBandW2 Q n J weights ω).restrict hR)
    have hfour := ht.mono_exponent (by norm_num : (2:ENNReal) ≤ ⊤)
    simpa only [hrestr, later_band_w2_value, f, n] using hfour
  have hQmean : |cubeAverage Q f - f (cubeCenter Q)| ≤ B*cubeScaleFactor Q/2 :=
    cube_average_deviation_le Q f (f (cubeCenter Q)) (B*cubeScaleFactor Q/2)
      hrootMem hpoint
  have hRpoint (x : Vec 2) (hx : x ∈ cubeSet R) :
      |f x - f (cubeCenter Q)| ≤ B * cubeScaleFactor Q / 2 :=
    hpoint x ((cubeSet_subset_of_mem_descendantsAtDepth hR) hx)
  have hRmean : |cubeAverage R f - f (cubeCenter Q)| ≤ B*cubeScaleFactor Q/2 :=
    cube_average_deviation_le R f (f (cubeCenter Q)) (B*cubeScaleFactor Q/2)
      hRmem hRpoint
  have hmeans : |cubeAverage R f - cubeAverage Q f| ≤ B*cubeScaleFactor Q := by
    have heq : cubeAverage R f - cubeAverage Q f =
        (cubeAverage R f - f (cubeCenter Q)) +
          (f (cubeCenter Q) - cubeAverage Q f) := by ring
    have hQmean' : |f (cubeCenter Q) - cubeAverage Q f| ≤ B*cubeScaleFactor Q/2 := by
      simpa only [abs_sub_comm] using hQmean
    rw [heq]
    calc
      |cubeAverage R f - f (cubeCenter Q) + (f (cubeCenter Q) - cubeAverage Q f)| ≤
          |cubeAverage R f - f (cubeCenter Q)| +
            |f (cubeCenter Q) - cubeAverage Q f| := abs_add_le _ _
      _ ≤ B*cubeScaleFactor Q/2 + B*cubeScaleFactor Q/2 := add_le_add hRmean hQmean'
      _ = B*cubeScaleFactor Q := by ring
  have hfinal : |cubeAverage R f / σ - cubeAverage Q f / σ| ≤ 10 * η := by
    have hdiff : cubeAverage R f / σ - cubeAverage Q f / σ =
        (cubeAverage R f - cubeAverage Q f) / σ := by ring
    rw [hdiff, abs_div, abs_of_pos hσ]
    apply (div_le_iff₀ hσ).2
    calc
      |cubeAverage R f - cubeAverage Q f| ≤ B*cubeScaleFactor Q := hmeans
      _ ≤ σ * (10 * η) := hBscaled
      _ = (10 * η) * σ := by ring
  simpa only [f, n, σ, hrestr, later_band_w2_value] using hfinal

end
end ASDExplicitGamma.Inverse
