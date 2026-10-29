module

public import ASDExplicitGamma.Model.Cstar
public import ASDExplicitGamma.Model.ShellScaling
public import Algsuperdiff.Section3.Provider.Corrector.ShellSumLayerDilation

@[expose] public section

open MeasureTheory Homogenization
open Algsuperdiff.Probability.Stationary
open Algsuperdiff.Section3.Provider.Corrector

namespace ASDExplicitGamma.Model

/-- Scaling of the unprojected forcing norm, on the common sequence carrier. -/
theorem norm_layerForcingL2_scale {d : ℕ}
    (M : Algsuperdiff.Section3.ABKModel d) (e : Vec d) (k : ℤ) :
    ‖layerForcingL2 M e k‖ = (3 : ℝ) ^ (M.gamma * (k : ℝ)) *
      ‖shellSumForcingL2 M e (0 - 1) 0‖ := by
  have h₀ := norm_carrierTransport (measurePreserving_seqPathCoord M k)
    (shellSumForcingL2 M e (k - 1) k)
  rw [carrierTransport_seqPathCoord_shellSumForcingL2] at h₀
  have h₁ := norm_carrierTransport (measurePreserving_pathScale M k)
    (shellSumForcingL2 M e (k - 1) k)
  rw [carrierTransport_pathScale_shellSumForcingL2, norm_smul,
    Real.norm_of_nonneg (by positivity)] at h₁
  exact h₀.trans h₁.symm

/-- The negative-level tail of the completed forcing is absolutely summable
in the stationary Hilbert space. -/
theorem summable_norm_completedLayerForcing {d : ℕ}
    (M : Algsuperdiff.Section3.ABKModel d) (e : Vec d) (m : ℤ) :
    Summable (fun n : ℕ => ‖layerForcingL2 M e (m - (n : ℤ))‖) := by
  have hr₀ : 0 ≤ (3 : ℝ) ^ (-M.gamma) := by positivity
  have hr₁ : (3 : ℝ) ^ (-M.gamma) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos M.shellPrefix.gamma_pos)
  have hs := (summable_geometric_of_lt_one hr₀ hr₁).mul_left
    ((3 : ℝ) ^ (M.gamma * (m : ℝ)) * ‖shellSumForcingL2 M e (0 - 1) 0‖)
  apply hs.congr
  intro n
  rw [norm_layerForcingL2_scale]
  have he : M.gamma * ((m - (n : ℤ) : ℤ) : ℝ) =
      M.gamma * (m : ℝ) + (-M.gamma) * (n : ℝ) := by push_cast; ring
  rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
  ring

/-- Absolute summability implies convergence of the completed forcing. -/
theorem summable_completedLayerForcing {d : ℕ}
    (M : Algsuperdiff.Section3.ABKModel d) (e : Vec d) (m : ℤ) :
    Summable (fun n : ℕ => layerForcingL2 M e (m - (n : ℤ))) :=
  (summable_norm_completedLayerForcing M e m).of_norm

/-- The genuine completed forcing on the jointly measurable path-sequence
carrier, as the convergent sum of all shell levels through `m`. -/
noncomputable def completedLayerForcingL2 {d : ℕ}
    (M : Algsuperdiff.Section3.ABKModel d) (e : Vec d) (m : ℤ) :
    Algsuperdiff.Probability.Stationary.VectorL2 d (seqPathLaw M.P).toMeasure :=
  ∑' n : ℕ, layerForcingL2 M e (m - (n : ℤ))

/-- Pythagoras for an absolutely summable orthogonal family. -/
theorem norm_sq_tsum_of_pairwise_inner_eq_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : ℕ → H} (hf : Summable f)
    (horth : ∀ i j, i ≠ j → inner ℝ (f i) (f j) = 0) :
    ‖∑' i, f i‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  change (innerSL ℝ (∑' i, f i)) (∑' i, f i) = _
  rw [(innerSL ℝ (∑' i, f i)).map_tsum hf]
  apply tsum_congr
  intro i
  change inner ℝ (∑' j, f j) (f i) = _
  rw [real_inner_comm]
  change (innerSL ℝ (f i)) (∑' j, f j) = _
  rw [(innerSL ℝ (f i)).map_tsum hf, tsum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j hji
    exact horth i j hji.symm

/-- The J4 projection energy of the completed, infinite cutoff is the full
geometric sum of the projected-shell energies. -/
theorem completedLayerForcing_projection_energy {d : ℕ}
    (M : Algsuperdiff.Section3.ABKModel d)
    {e : Vec d} (he : Book.Ch02.vecNorm e = 1) (m : ℤ) :
    ‖stationaryPotentialProjection (completedLayerForcingL2 M e m)‖ ^ 2 =
      Algsuperdiff.Section3.Disorder.cstar M * Real.log 3 *
        (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) /
          (1 - (3 : ℝ) ^ (-(2 * M.gamma))) := by
  let P := stationaryPotentialProjection (d := d) (μ := (seqPathLaw M.P).toMeasure)
  have hs := summable_completedLayerForcing M e m
  have hps : Summable (fun n : ℕ => P (layerForcingL2 M e (m - (n : ℤ)))) :=
    hs.mapL P
  change ‖P (∑' n : ℕ, layerForcingL2 M e (m - (n : ℤ)))‖ ^ 2 = _
  rw [P.map_tsum hs]
  rw [norm_sq_tsum_of_pairwise_inner_eq_zero hps]
  · have hterm (n : ℕ) : ‖P (layerForcingL2 M e (m - (n : ℤ)))‖ ^ 2 =
        Algsuperdiff.Section3.Disorder.cstar M * Real.log 3 *
          (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)) *
            ((3 : ℝ) ^ (-(2 * M.gamma))) ^ n := by
      dsimp [P]
      rw [norm_sq_stationaryPotentialProjection_layerForcingL2,
        norm_sq_stationaryPotentialProjection_layerForcingL2_zero M he]
      have he' : 2 * M.gamma * ((m - (n : ℤ) : ℤ) : ℝ) =
          2 * M.gamma * (m : ℝ) + (-(2 * M.gamma)) * (n : ℝ) := by push_cast; ring
      rw [he', Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)]
      ring
    simp_rw [hterm]
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    · rfl
    · positivity
    · exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        (by linarith [M.shellPrefix.gamma_pos])
  · intro i j hij
    apply inner_stationaryPotentialProjection_layerForcingL2_eq_zero
    omega

/-- For the planar q3 model, the completed stationary projected energy is
exactly half the accumulated stream variance. -/
theorem q3_completedLayerForcing_projection_energy
    (M : Algsuperdiff.Section3.ABKModel 2) (h : ℝ)
    (hM : ASDExplicitGamma.PlanarQ3Gaussian M h)
    {e : Vec 2} (he : Book.Ch02.vecNorm e = 1) (m : ℤ) :
    ‖stationaryPotentialProjection (completedLayerForcingL2 M e m)‖ ^ 2 =
      shellVarianceSum h M.gamma m / 2 := by
  rw [completedLayerForcing_projection_energy M he m, q3_cstar_exact M h hM]
  have hlog : Real.log (3 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold shellVarianceSum
  field_simp

end ASDExplicitGamma.Model
