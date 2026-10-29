module

public import ASDExplicitGamma.Triadic.DiagBessel
public import ASDExplicitGamma.Triadic.PoincareCell
public import ASDExplicitGamma.Triadic.Support.ProjectedPoincare.Geometry
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact moments and positive-Haar norm of the centered cell coordinate. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

/-- Coordinate measured from the negative face and centered at one half. -/
def diagCenteredCoordinate (Q : TriadicCube 2) (i : Fin 2) (x : Vec 2) : ℝ :=
  (x i - cubeCorner Q i) / cubeScaleFactor Q - 1 / 2

theorem diagInterval_probability (a : ℝ) {L : ℝ} (hL : 0 < L) :
    IsProbabilityMeasure (ENNReal.ofReal L⁻¹ • volume.restrict (Ico a (a + L))) := by
  constructor
  rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, Real.volume_Ico]
  have heq : a + L - a = L := by ring
  rw [heq, ← ENNReal.ofReal_mul (inv_nonneg.mpr hL.le), inv_mul_cancel₀ hL.ne']
  norm_num

/-- The exact marginal integral of any measurable coordinate function. -/
theorem diagCoordinate_integral (Q : TriadicCube 2) (i : Fin 2) (f : ℝ → ℝ)
    (hf : Measurable f) :
    (∫ x, f (x i) ∂normalizedCubeMeasure Q) =
      (cubeScaleFactor Q)⁻¹ * ∫ t in cubeCorner Q i..cubeCorner Q i + cubeScaleFactor Q, f t := by
  let L := cubeScaleFactor Q
  have hL := cubeScaleFactor_pos' Q
  let μ : Fin 2 → Measure ℝ := fun k => ENNReal.ofReal L⁻¹ •
    volume.restrict (Ico (cubeCorner Q k) (cubeCorner Q k + L))
  have diagCoordinateProbability (k : Fin 2) : IsProbabilityMeasure (μ k) :=
    diagInterval_probability _ hL
  rw [← boxMeasure_eq_normalizedCubeMeasure]
  change (∫ x, f (x i) ∂Measure.pi μ) = _
  rw [integral_comp_eval hf.aestronglyMeasurable]
  change (∫ t, f t ∂(ENNReal.ofReal L⁻¹ • volume.restrict
    (Ico (cubeCorner Q i) (cubeCorner Q i + L)))) = _
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hL.le),
    smul_eq_mul, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [hL])]

/-- Normalized first moment of the centered coordinate. -/
theorem diagCenteredCoordinate_mean (Q : TriadicCube 2) (i : Fin 2) :
    cubeAverage Q (diagCenteredCoordinate Q i) = 0 := by
  let a := cubeCorner Q i
  let L := cubeScaleFactor Q
  have hL : L ≠ 0 := (cubeScaleFactor_pos' Q).ne'
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  change (∫ x, ((x i - a) / L - 1 / 2) ∂normalizedCubeMeasure Q) = 0
  rw [diagCoordinate_integral Q i (fun t => (t - a) / L - 1 / 2) (by fun_prop)]
  have hderiv (t : ℝ) : HasDerivAt
      (fun x => (x - a) ^ 2 / (2 * L) - (x - a) / 2) ((t - a) / L - 1 / 2) t := by
    convert ((((hasDerivAt_id t).sub_const a).pow 2).div_const (2 * L)).sub
      (((hasDerivAt_id t).sub_const a).div_const 2) using 1
    · funext x
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq]
      field_simp [hL]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (by exact (show Continuous (fun t : ℝ => (t - a) / L - 1 / 2) by fun_prop).intervalIntegrable _ _)]
  dsimp only [a, L]
  field_simp [(cubeScaleFactor_pos' Q).ne']
  ring

/-- Normalized second moment of the centered coordinate. -/
theorem diagCenteredCoordinate_energy (Q : TriadicCube 2) (i : Fin 2) :
    energy Q (diagCenteredCoordinate Q i) = 1 / 12 := by
  let a := cubeCorner Q i
  let L := cubeScaleFactor Q
  have hL : L ≠ 0 := (cubeScaleFactor_pos' Q).ne'
  rw [energy_eq_integral_sq]
  change (∫ x, ((x i - a) / L - 1 / 2) ^ 2 ∂normalizedCubeMeasure Q) = 1 / 12
  rw [diagCoordinate_integral Q i (fun t => ((t - a) / L - 1 / 2) ^ 2) (by fun_prop)]
  have hderiv (t : ℝ) : HasDerivAt
      (fun x => (x - a - L / 2) ^ 3 / (3 * L ^ 2)) (((t - a) / L - 1 / 2) ^ 2) t := by
    convert ((((hasDerivAt_id t).sub_const a).sub_const (L / 2)).pow 3).div_const (3 * L ^ 2)
      using 1
    · funext x
      simp only [Pi.pow_apply, id_eq]
    · simp only [id_eq]
      field_simp [hL]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    (by exact (show Continuous (fun t : ℝ => ((t - a) / L - 1 / 2) ^ 2) by fun_prop).intervalIntegrable _ _)]
  dsimp only [a, L]
  field_simp [(cubeScaleFactor_pos' Q).ne']
  ring

theorem diagCenteredCoordinate_memLp (Q : TriadicCube 2) (i : Fin 2) :
    MemLp (diagCenteredCoordinate Q i) 2 (normalizedCubeMeasure Q) :=
  Support.ProjectedPoincare.continuous_memLp_cube Q (by unfold diagCenteredCoordinate; fun_prop) 2

/-- A parent coordinate restricts to an affine multiple of the local coordinate. -/
theorem diagCenteredCoordinate_affine (Q R : TriadicCube 2) (i : Fin 2) (x : Vec 2) :
    diagCenteredCoordinate Q i x = cubeScaleFactor R / cubeScaleFactor Q *
      diagCenteredCoordinate R i x +
        ((cubeCorner R i - cubeCorner Q i) / cubeScaleFactor Q +
          cubeScaleFactor R / (2 * cubeScaleFactor Q) - 1 / 2) := by
  unfold diagCenteredCoordinate
  field_simp [(cubeScaleFactor_pos' Q).ne', (cubeScaleFactor_pos' R).ne']
  ring

/-- Exact local mean of a parent coordinate. -/
theorem diagCenteredCoordinate_local_mean (Q R : TriadicCube 2) (i : Fin 2) :
    cubeAverage R (diagCenteredCoordinate Q i) =
      (cubeCorner R i - cubeCorner Q i) / cubeScaleFactor Q +
        cubeScaleFactor R / (2 * cubeScaleFactor Q) - 1 / 2 := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  simp_rw [diagCenteredCoordinate_affine Q R i]
  rw [integral_add
      (((diagCenteredCoordinate_memLp R i).integrable one_le_two).const_mul (cubeScaleFactor R / cubeScaleFactor Q)) (integrable_const _),
    integral_const_mul, ← cubeAverage_eq_integral_normalizedCubeMeasure,
    diagCenteredCoordinate_mean, mul_zero, zero_add,
    ← cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage_const]

/-- Exact variance on a descendant, scaled by its side. -/
theorem diagCenteredCoordinate_local_variance (Q R : TriadicCube 2) (i : Fin 2) :
    energy R (fun x => diagCenteredCoordinate Q i x - cubeAverage R (diagCenteredCoordinate Q i)) =
      (cubeScaleFactor R / cubeScaleFactor Q) ^ 2 / 12 := by
  have heq : (fun x => diagCenteredCoordinate Q i x - cubeAverage R (diagCenteredCoordinate Q i)) =
      (fun x => (cubeScaleFactor R / cubeScaleFactor Q) * diagCenteredCoordinate R i x) := by
    funext x
    rw [diagCenteredCoordinate_affine Q R i, diagCenteredCoordinate_local_mean]
    ring
  rw [heq]
  unfold energy pairing
  simp_rw [show ∀ x : Vec 2, (cubeScaleFactor R / cubeScaleFactor Q * diagCenteredCoordinate R i x) *
      (cubeScaleFactor R / cubeScaleFactor Q * diagCenteredCoordinate R i x) =
      (cubeScaleFactor R / cubeScaleFactor Q) ^ 2 *
        (diagCenteredCoordinate R i x * diagCenteredCoordinate R i x) from fun x => by ring]
  rw [cubeAverage_eq_integral_normalizedCubeMeasure, integral_const_mul,
    ← cubeAverage_eq_integral_normalizedCubeMeasure]
  change (cubeScaleFactor R / cubeScaleFactor Q) ^ 2 * energy R (diagCenteredCoordinate R i) = _
  rw [diagCenteredCoordinate_energy]
  ring

/-- Exact projection residual variance at every complete triadic depth. -/
theorem diagCenteredCoordinate_residual_energy (Q : TriadicCube 2) (i : Fin 2) (j : ℕ) :
    energy Q (fun x => diagCenteredCoordinate Q i x - cubeProjection Q j (diagCenteredCoordinate Q i) x) =
      1 / (12 * (9 : ℝ) ^ j) := by
  have hf := diagCenteredCoordinate_memLp Q i
  have hmem : MemLp (fun x => diagCenteredCoordinate Q i x -
      cubeProjection Q j (diagCenteredCoordinate Q i) x) 2 (normalizedCubeMeasure Q) :=
    hf.sub (projection_memLp Q j (diagCenteredCoordinate Q i) 2)
  rw [energy_eq_descendantsAverage Q j hmem]
  have hcell (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
      energy R (fun x => diagCenteredCoordinate Q i x - cubeProjection Q j (diagCenteredCoordinate Q i) x) =
        1 / (12 * (9 : ℝ) ^ j) := by
    have heq : energy R (fun x => diagCenteredCoordinate Q i x - cubeProjection Q j (diagCenteredCoordinate Q i) x) =
        energy R (fun x => diagCenteredCoordinate Q i x - cubeAverage R (diagCenteredCoordinate Q i)) := by
      unfold energy pairing
      apply cubeAverage_congr_on_cubeSet
      intro x hx
      beta_reduce
      rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hx]
    rw [heq, diagCenteredCoordinate_local_variance, cubeScaleFactor_descendant_eq_div_pow hR]
    have hp : (9 : ℝ) ^ j = ((3 : ℝ) ^ j) ^ 2 := by
      rw [← pow_mul, mul_comm j 2, pow_mul]
      norm_num
    rw [hp]
    field_simp [(cubeScaleFactor_pos' Q).ne']
  dsimp only [descendantsAverage]
  have hsum : (∑ R ∈ descendantsAtDepth Q j,
      energy R (fun x => diagCenteredCoordinate Q i x - cubeProjection Q j (diagCenteredCoordinate Q i) x)) =
        (descendantsAtDepth Q j).card * (1 / (12 * (9 : ℝ) ^ j)) := by
    rw [Finset.sum_congr rfl (fun R hR => hcell R hR), Finset.sum_const, nsmul_eq_mul]
  rw [hsum]
  have hc : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j))
  field_simp

/-- The centered-coordinate positive tail is an actual convergent series. -/
theorem diagCenteredCoordinate_residuals_summable (Q : TriadicCube 2) (i : Fin 2) :
    Summable (fun j => (Real.sqrt 3) ^ j * energy Q (fun x => diagCenteredCoordinate Q i x -
      cubeProjection Q j (diagCenteredCoordinate Q i) x)) := by
  have hq : Real.sqrt 3 / 9 < 1 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have h0 : 0 ≤ Real.sqrt 3 / 9 := by positivity
  have hgeom := (summable_geometric_of_lt_one h0 hq).mul_left (1 / 12 : ℝ)
  apply hgeom.congr
  intro j
  rw [diagCenteredCoordinate_residual_energy, div_pow]
  ring

theorem diagCenteredCoordinate_positive_summable (Q : TriadicCube 2) (i : Fin 2) :
    Summable (fun k => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (diagCenteredCoordinate Q i))) :=
  summable_primal_increments_of_residuals Q (Real.sqrt 3)
    (diagCenteredCoordinate_memLp Q i) (diagCenteredCoordinate_residuals_summable Q i)

/-- The exact positive-dual variance, including the root and all depths. -/
theorem diagCenteredCoordinate_positiveEnergy (Q : TriadicCube 2) (i : Fin 2) :
    primalEnergy Q (Real.sqrt 3) (diagCenteredCoordinate Q i) = diagWeakFaceVariance := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  have hq9 : Real.sqrt 3 / 9 < 1 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [primalEnergy_eq_abel Q hq (diagCenteredCoordinate_memLp Q i)
    (diagCenteredCoordinate_residuals_summable Q i), diagCenteredCoordinate_energy]
  have heq : (fun j => (Real.sqrt 3) ^ j * energy Q (fun x => diagCenteredCoordinate Q i x -
      cubeProjection Q j (diagCenteredCoordinate Q i) x)) =
        (fun j => (1 / 12 : ℝ) * (Real.sqrt 3 / 9) ^ j) := by
    funext j
    rw [diagCenteredCoordinate_residual_energy, div_pow]
    ring
  rw [heq, tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hq9]
  unfold diagWeakFaceVariance
  have hn : 9 - Real.sqrt 3 ≠ 0 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  field_simp
  ring

/-- The exact joint mean/face Bessel inequality, with source variance and
constant one. No zero boundary assumption is imposed on the gradient component. -/
theorem diagWeakFace_jointBessel (Q : TriadicCube 2) (i : Fin 2)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    (cubeAverage Q f) ^ 2 + (pairing Q f (diagCenteredCoordinate Q i)) ^ 2 /
      diagWeakFaceVariance ≤ dualEnergy Q (Real.sqrt 3) f := by
  have h := diagJointBessel Q hf (diagCenteredCoordinate_memLp Q i)
    (diagCenteredCoordinate_mean Q i) (diagCenteredCoordinate_positive_summable Q i)
  rw [diagCenteredCoordinate_positiveEnergy] at h
  have hvar : 0 < diagWeakFaceVariance := by
    have h0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    have h9 : Real.sqrt 3 < 9 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    unfold diagWeakFaceVariance
    positivity
  have hd : (pairing Q f (diagCenteredCoordinate Q i)) ^ 2 / diagWeakFaceVariance ≤
      dualEnergy Q (Real.sqrt 3) f - (cubeAverage Q f) ^ 2 := by
    apply (div_le_iff₀ hvar).2
    nlinarith only [h]
  linarith only [hd]

end

end ASDExplicitGamma.Triadic
