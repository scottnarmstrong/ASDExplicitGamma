module

public import ASDExplicitGamma.Triadic.TriadicProjection
public import ASDExplicitGamma.Triadic.Support.ProjectedPoincare.Geometry
public import ASDExplicitGamma.Triadic.PlanarDirectionOperations
public import ASDExplicitGamma.Inverse.PhysicalGaussianMissingWave
public import ASDExplicitGamma.Inverse.LaterBandW2

/-! The local later-wave mean is paid by the root spatial fourth moment
with the exact descendant-volume factor. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic
open ASDExplicitGamma.Model
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic.Support.ProjectedPoincare

noncomputable section

/-- The normalized fourth moment on a triadic parent is the ordinary fourth
moment on the matching physical square, divided by its area. -/
theorem cube_average_fourth_eq_physical_square_integral
    (Q : TriadicCube 2) (f : Vec 2 → ℝ) :
    cubeAverage Q (fun x => f x ^ 4) =
      (cubeScaleFactor Q)⁻¹ ^ 2 *
        ∫ x : closedRectangle (cubeCorner Q 0)
            (cubeCorner Q 0 + cubeScaleFactor Q)
            (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q),
          f x.1 ^ 4 ∂spatialVolume
            (closedRectangle (cubeCorner Q 0)
              (cubeCorner Q 0 + cubeScaleFactor Q)
              (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q)) := by
  classical
  let a := cubeCorner Q 0
  let c := cubeCorner Q 1
  let R := cubeScaleFactor Q
  let K := closedRectangle a (a + R) c (c + R)
  have hUpper (i : Fin 2) : cubeCorner Q i + cubeScaleFactor Q =
      ((Q.index i : ℝ) + 1 / 2) * cubeScaleFactor Q := by
    simp only [cubeCorner]
    ring
  have hOpen : openCubeSet Q = openRectangle a (a + R) c (c + R) := by
    rw [openCubeSet_eq_box]
    ext x
    simp only [Set.mem_pi, Set.mem_univ, true_implies, openRectangle,
      Set.mem_ofPred_eq, Set.mem_Ioo]
    constructor
    · intro hx
      refine ⟨?_, ?_⟩
      · exact ⟨by simpa [a] using (hx 0).1,
          by simpa [a, R, hUpper 0] using (hx 0).2⟩
      · exact ⟨by simpa [c] using (hx 1).1,
          by simpa [c, R, hUpper 1] using (hx 1).2⟩
    · rintro ⟨hx0, hx1⟩ i
      fin_cases i
      · exact ⟨by simpa [a, cubeCorner] using hx0.1,
          by simpa [a, R, hUpper 0] using hx0.2⟩
      · exact ⟨by simpa [c, cubeCorner] using hx1.1,
          by simpa [c, R, hUpper 1] using hx1.2⟩
  have hRectIntegral :
      (∫ x in openRectangle a (a + R) c (c + R), f x ^ 4 ∂volume) =
        ∫ x : K, f x.1 ^ 4 ∂spatialVolume K := by
    calc
      _ = ∫ x in K, f x ^ 4 ∂volume := by
        rw [rectangle_restrict_eq]
      _ = _ := (integral_subtype_comap
        (closedRectangle_isCompact a (a + R) c (c + R)).isClosed.measurableSet
        (fun x => f x ^ 4)).symm
  have hmean : cubeAverage Q (fun x => f x ^ 4) =
      (cubeVolume Q)⁻¹ * ∫ x in openCubeSet Q, f x ^ 4 ∂volume := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, integral_normalized_eq_open]
  rw [hmean, hOpen, hRectIntegral]
  congr 1
  have hVol : cubeVolume Q = (cubeScaleFactor Q) ^ 2 := by
    rw [cubeVolume_eq_scaleFactor_pow]
  rw [hVol]
  rw [← inv_pow]

/-- The literal scalar later-shell band is the physical shell-field band on
the triadic cube's matching closed square. -/
theorem later_scalar_band_eq_whole_root_model_band
    (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    let K := closedRectangle (cubeCorner Q 0)
      (cubeCorner Q 0 + cubeScaleFactor Q)
      (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q)
    (fun x : K => laterScalarBand n J weights ω x.1) =
      wholeRootModelBand (a := cubeCorner Q 0)
        (b := cubeCorner Q 0 + cubeScaleFactor Q)
        (c := cubeCorner Q 1)
        (d := cubeCorner Q 1 + cubeScaleFactor Q) n J weights ω := by
  classical
  dsimp only
  let K := closedRectangle (cubeCorner Q 0)
    (cubeCorner Q 0 + cubeScaleFactor Q)
    (cubeCorner Q 1) (cubeCorner Q 1 + cubeScaleFactor Q)
  funext x
  simp only [laterScalarBand, wholeRootModelBand, modelWeightedBand,
    wholeRootWeights, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  have hscalar (k : ℤ) :
      shellFieldScalarRestriction K (ω.1 k) x =
        shellScalarValue (ω.val k) x.1 := by
    rfl
  let f : ℤ → ℝ := fun k => weights k * shellScalarValue (ω.val k) x.1
  have hsum :
      (∑ i : Fin (wholeRootBandLength n J), f (wholeRootShellLabel n J i)) =
        ∑ k ∈ Finset.Ioc n J, f k :=
    wholeRootShellLabel_sum_Ioc n J f
  calc
    _ = ∑ k ∈ Finset.Ioc n J, f k := by
      simp [f]
    _ = ∑ i : Fin (wholeRootBandLength n J),
          f (wholeRootShellLabel n J i) := hsum.symm
    _ = ∑ i : Fin (wholeRootBandLength n J),
          weights (wholeRootShellLabel n J i) *
            shellFieldScalarRestriction K
              (ω.1 (wholeRootShellLabel n J i)) x := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [f]
      rw [← hscalar]

/-- On its own triadic square, a physical missing wave is exactly twice the
normalized scalar fourth-moment root in the true old frame. -/
theorem later_band_physical_missing_wave_eq_fourth_average
    (A : ABKModel 2) (R : TriadicCube 2) (j J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    physicalMissingWave A j R.scale J (cubeCorner R 0) (cubeCorner R 1)
        weights ω =
      (2 / (Annealed.sigmaBar A j : ℝ) ^ 2) *
        Real.sqrt (cubeAverage R
          (fun x => laterScalarBand j J weights ω x ^ 4)) := by
  classical
  let L := cubeScaleFactor R
  let a := cubeCorner R 0
  let c := cubeCorner R 1
  let K := closedRectangle a (a + L) c (c + L)
  let F : C(K, ℝ) := wholeRootModelBand
    (a := a) (b := a + L) (c := c) (d := c + L) j J weights ω
  let f : Vec 2 → ℝ := laterScalarBand j J weights ω
  have hside : L = (3 : ℝ) ^ R.scale := by
    rfl
  have hL : 0 < L := by
    dsimp only [L]
    exact ASDExplicitGamma.Triadic.cubeScaleFactor_pos' R
  have hσ : 0 < (Annealed.sigmaBar A j : ℝ) :=
    (Annealed.sigmaBar_characterization A j).1
  have hband : (fun x : K => f x.1) = F := by
    simpa only [K, a, c, L, f, F] using
      later_scalar_band_eq_whole_root_model_band R j J weights ω
  have hInt : (∫ x : K, f x.1 ^ 4 ∂spatialVolume K) =
      ‖ContinuousMap.toLp 4 (spatialVolume K) ℝ F‖ ^ 4 := by
    calc
      _ = ∫ x : K, F x ^ 4 ∂spatialVolume K := by
        apply integral_congr_ae
        filter_upwards with x
        exact congrArg (fun y : ℝ => y ^ 4) (congrFun hband x)
      _ = _ := (continuousMap_toLp_norm_pow_four (spatialVolume K) F).symm
  have hAvg := cube_average_fourth_eq_physical_square_integral R f
  have hAvg0 : 0 ≤ cubeAverage R (fun x => f x ^ 4) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    exact integral_nonneg fun x => by positivity
  have hNormRoot :
      Real.sqrt (cubeAverage R (fun x => f x ^ 4)) =
        ‖ContinuousMap.toLp 4 (spatialVolume K) ℝ F‖ ^ 2 / L := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (div_nonneg (sq_nonneg _) hL.le)).mp
    calc
      (Real.sqrt (cubeAverage R (fun x => f x ^ 4))) ^ 2 =
          cubeAverage R (fun x => f x ^ 4) := Real.sq_sqrt hAvg0
      _ = L⁻¹ ^ 2 * ‖ContinuousMap.toLp 4 (spatialVolume K) ℝ F‖ ^ 4 := by
        rw [hAvg, hInt]
      _ = (‖ContinuousMap.toLp 4 (spatialVolume K) ℝ F‖ ^ 2 / L) ^ 2 := by
        field_simp [hL.ne']
  have hphysical :
      physicalMissingWave A j R.scale J a c weights ω =
        wholeRootSpatialStatistic (Annealed.sigmaBar A j : ℝ) L F := by
    rw [physical_missing_wave_eq_frobenius, ← hside]
    change normalizedFrobeniusL4Squared (Annealed.sigmaBar A j : ℝ) L F =
      wholeRootSpatialStatistic (Annealed.sigmaBar A j : ℝ) L F
    exact normalizedFrobeniusL4Squared_eq_spatialStatistic
      (K := K) (Annealed.sigmaBar A j : ℝ) L hσ hL F
  rw [hphysical, wholeRootSpatialStatistic, hNormRoot]
  field_simp [hσ.ne', hL.ne']

end
end ASDExplicitGamma.Inverse
