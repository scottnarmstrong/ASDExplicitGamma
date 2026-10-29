module

public import ASDExplicitGamma.Triadic.PlanarPositiveGradient
public import ASDExplicitGamma.Triadic.PlanarSobolev
public import ASDExplicitGamma.Triadic.PlanarNeumannBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic.FinCases

/-! The vector-valued weak-gradient multiplier estimate on planar cubes. -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Triadic

private theorem planarSqrtSqSum_le_absSum (x : Fin 2 → ℝ) :
    planarEuclideanNorm x ≤ ∑ i, |x i| := by
  simp only [planarEuclideanNorm, Fin.sum_univ_two]
  have h0 := abs_nonneg (x 0)
  have h1 := abs_nonneg (x 1)
  apply (Real.sqrt_le_iff).2 ⟨add_nonneg h0 h1, ?_⟩
  nlinarith [sq_abs (x 0), sq_abs (x 1)]

private theorem planarFrobSqrtSqSum_le_absSum (A : Fin 2 → Fin 2 → ℝ) :
    planarFrobeniusNorm A ≤ ∑ i, ∑ j, |A i j| := by
  simp only [planarFrobeniusNorm, Fin.sum_univ_two]
  have h00 := abs_nonneg (A 0 0)
  have h01 := abs_nonneg (A 0 1)
  have h10 := abs_nonneg (A 1 0)
  have h11 := abs_nonneg (A 1 1)
  apply (Real.sqrt_le_iff).2 ⟨by positivity, ?_⟩
  nlinarith [sq_abs (A 0 0), sq_abs (A 0 1), sq_abs (A 1 0), sq_abs (A 1 1)]

private theorem planarW1Value_memLp_top {Q : TriadicCube 2}
    (b : PlanarW1Infinity Q) :
    MemLp (fun x => planarEuclideanNorm (planarW1Value b x)) ⊤
      (normalizedCubeMeasure Q) := by
  let μ := normalizedCubeMeasure Q
  let g : Vec 2 → ℝ := fun x => ∑ i, |planarW1Value b x i|
  have hg : MemLp g ⊤ μ := by
    dsimp [g]
    apply memLp_finsetSum Finset.univ
    intro i hi
    simpa [planarW1Value] using (b.component_memLp_top i).norm
  have hmeas : AEStronglyMeasurable
      (fun x => planarEuclideanNorm (planarW1Value b x)) μ := by
    have h0 := (b.component_memLp_top 0).aestronglyMeasurable
    have h1 := (b.component_memLp_top 1).aestronglyMeasurable
    have hs : AEStronglyMeasurable[MeasureSpace.pi.toMeasurableSpace]
        (fun x : Vec 2 => ∑ i : Fin 2, (planarW1Value b x i) ^ 2) μ := by
      convert (h0.pow 2).add (h1.pow 2) using 1
      ext x
      simp [Fin.sum_univ_two, planarW1Value]
    have hc : AEStronglyMeasurable[MeasureSpace.pi.toMeasurableSpace]
        (fun x => planarEuclideanNorm (planarW1Value b x)) μ := by
      simpa only [planarEuclideanNorm] using Real.continuous_sqrt.comp_aestronglyMeasurable hs
    exact hc
  apply hg.mono' hmeas
  filter_upwards with x
  change |planarEuclideanNorm (planarW1Value b x)| ≤ g x
  rw [abs_of_nonneg (by unfold planarEuclideanNorm; exact Real.sqrt_nonneg _)]
  exact planarSqrtSqSum_le_absSum (planarW1Value b x)

private theorem planarW1Derivative_memLp_top {Q : TriadicCube 2}
    (b : PlanarW1Infinity Q) :
    MemLp (fun x => planarFrobeniusNorm (planarW1Derivative b x)) ⊤
      (normalizedCubeMeasure Q) := by
  let μ := normalizedCubeMeasure Q
  let g : Vec 2 → ℝ := fun x => ∑ i, ∑ j, |planarW1Derivative b x i j|
  have hg : MemLp g ⊤ μ := by
    dsimp [g]
    apply memLp_finsetSum Finset.univ
    intro i hi
    apply memLp_finsetSum Finset.univ
    intro j hj
    simpa [planarW1Derivative] using
      (b.derivative_memLp_top i j).norm
  have hmeas : AEStronglyMeasurable
      (fun x => planarFrobeniusNorm (planarW1Derivative b x)) μ := by
    have h00 := (b.derivative_memLp_top 0 0).aestronglyMeasurable
    have h01 := (b.derivative_memLp_top 0 1).aestronglyMeasurable
    have h10 := (b.derivative_memLp_top 1 0).aestronglyMeasurable
    have h11 := (b.derivative_memLp_top 1 1).aestronglyMeasurable
    have hs : AEStronglyMeasurable[MeasureSpace.pi.toMeasurableSpace]
        (fun x : Vec 2 => ∑ i : Fin 2, ∑ j : Fin 2,
          (planarW1Derivative b x i j) ^ 2) μ := by
      convert (((h00.pow 2).add (h01.pow 2)).add ((h10.pow 2).add (h11.pow 2))) using 1
      ext x
      simp [Fin.sum_univ_two, planarW1Derivative]
    have hc : AEStronglyMeasurable[MeasureSpace.pi.toMeasurableSpace]
        (fun x => planarFrobeniusNorm (planarW1Derivative b x)) μ := by
      simpa only [planarFrobeniusNorm] using Real.continuous_sqrt.comp_aestronglyMeasurable hs
    exact hc
  apply hg.mono' hmeas
  filter_upwards with x
  change |planarFrobeniusNorm (planarW1Derivative b x)| ≤ g x
  rw [abs_of_nonneg (by unfold planarFrobeniusNorm; exact Real.sqrt_nonneg _)]
  exact planarFrobSqrtSqSum_le_absSum (planarW1Derivative b x)

/-- The weak-gradient data in `PlanarW1Infinity` imply the vector essential
supremum bound represented by `planarW1ValueLInf`. -/
theorem ae_planarW1Value_le_linf {Q : TriadicCube 2}
    (b : PlanarW1Infinity Q) :
    ∀ᵐ x ∂(normalizedCubeMeasure Q),
      planarEuclideanNorm (planarW1Value b x) ≤ planarW1ValueLInf b := by
  have h := ae_le_lpNorm_exponent_top (planarW1Value_memLp_top b)
  simpa [planarW1ValueLInf, planarEuclideanNorm, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), toReal_eLpNorm] using h

/-- The weak derivative data in `PlanarW1Infinity` imply the Frobenius
essential supremum bound represented by `planarW1DerivativeFrobeniusLInf`. -/
theorem ae_planarW1Derivative_le_linf {Q : TriadicCube 2}
    (b : PlanarW1Infinity Q) :
    ∀ᵐ x ∂(normalizedCubeMeasure Q),
      planarFrobeniusNorm (planarW1Derivative b x) ≤
        planarW1DerivativeFrobeniusLInf b := by
  have h := ae_le_lpNorm_exponent_top (planarW1Derivative_memLp_top b)
  simpa [planarW1DerivativeFrobeniusLInf, planarFrobeniusNorm, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), toReal_eLpNorm] using h

/-- The pointwise `L∞` bound controls the vector `L²` norm of a product. -/
theorem vectorEnergy_mul_le_linf (Q : TriadicCube 2) (b : PlanarW1Infinity Q)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    ∑ i : Fin 2, energy Q (fun x => planarW1Value b x i * f x) ≤
      planarW1ValueLInf b ^ 2 * energy Q f := by
  let μ := normalizedCubeMeasure Q
  let M := planarW1ValueLInf b
  have hM : 0 ≤ M := by
    dsimp [M, planarW1ValueLInf]
    positivity
  have hprod : ∀ i : Fin 2,
      MemLp (fun x => planarW1Value b x i * f x) 2 μ := by
    intro i
    exact (b.component_memLp_top i).mul hf
  have hprodInt : ∀ i : Fin 2,
      Integrable (fun x => (planarW1Value b x i * f x) ^ 2) μ := by
    intro i
    have heq : (fun x => (planarW1Value b x i * f x) ^ 2) =
        (fun x => planarW1Value b x i * f x) *
          (fun x => planarW1Value b x i * f x) := by
      funext x
      simp only [pow_two, Pi.mul_apply]
    rw [heq]
    exact (hprod i).integrable_mul (hprod i)
  have hfInt : Integrable (fun x => f x ^ 2) μ := by
    have heq : (fun x => f x ^ 2) = (fun x => f x) * (fun x => f x) := by
      funext x
      simp only [pow_two, Pi.mul_apply]
    rw [heq]
    exact hf.integrable_mul hf
  have hupperInt : Integrable (fun x => M ^ 2 * f x ^ 2) μ := hfInt.const_mul _
  have hpoint : ∀ᵐ x ∂μ,
      (∑ i : Fin 2, (planarW1Value b x i * f x) ^ 2) ≤ M ^ 2 * f x ^ 2 := by
    filter_upwards [ae_planarW1Value_le_linf b] with x hx
    have hnorm : planarEuclideanNorm (planarW1Value b x) ^ 2 =
        ∑ i : Fin 2, planarW1Value b x i ^ 2 := by
      unfold planarEuclideanNorm
      exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hsq : (∑ i : Fin 2, planarW1Value b x i ^ 2) ≤ M ^ 2 := by
      rw [← hnorm]
      have hx' : planarEuclideanNorm (planarW1Value b x) ≤ M := by simpa [M] using hx
      exact (sq_le_sq₀ (by unfold planarEuclideanNorm; positivity) hM).2 hx'
    calc
      (∑ i : Fin 2, (planarW1Value b x i * f x) ^ 2) =
          f x ^ 2 * ∑ i : Fin 2, planarW1Value b x i ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ ≤ M ^ 2 * f x ^ 2 := by
            calc
              f x ^ 2 * ∑ i : Fin 2, planarW1Value b x i ^ 2 ≤
                  f x ^ 2 * M ^ 2 :=
                mul_le_mul_of_nonneg_left hsq (sq_nonneg (f x))
              _ = M ^ 2 * f x ^ 2 := by ring
  calc
    ∑ i : Fin 2, energy Q (fun x => planarW1Value b x i * f x) =
        ∫ x, ∑ i : Fin 2, (planarW1Value b x i * f x) ^ 2 ∂μ := by
          calc
            ∑ i : Fin 2, energy Q (fun x => planarW1Value b x i * f x) =
                ∑ i : Fin 2, ∫ x, (planarW1Value b x i * f x) ^ 2 ∂μ := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact energy_eq_integral_sq Q _
            _ = ∫ x, ∑ i : Fin 2, (planarW1Value b x i * f x) ^ 2 ∂μ :=
              (integral_finsetSum Finset.univ fun i hi => hprodInt i).symm
    _ ≤ ∫ x, M ^ 2 * f x ^ 2 ∂μ := integral_mono_ae
          (integrable_finsetSum Finset.univ fun i hi => hprodInt i) hupperInt hpoint
    _ = M ^ 2 * energy Q f := by
          rw [energy_eq_integral_sq Q, integral_const_mul]
    _ = planarW1ValueLInf b ^ 2 * energy Q f := rfl

private theorem ae_on_normalized_descendant (Q U : TriadicCube 2) (j : ℕ)
    (hU : U ∈ descendantsAtDepth Q j) {P : Vec 2 → Prop}
    (hP : ∀ᵐ x ∂(normalizedCubeMeasure Q), P x) :
    ∀ᵐ x ∂(normalizedCubeMeasure U), P x := by
  rw [normalizedCubeMeasure_descendant_eq_smul_restrict hU]
  exact Measure.ae_smul_measure (hP.filter_mono ae_restrict_le) _

/-- The Hessian-style Frobenius essential bound controls the sum of derivative
energies on every descendant, with the same constant. -/
private theorem planarW1Derivative_energy_le_linf_sq (Q U : TriadicCube 2) (j : ℕ)
    (b : PlanarW1Infinity Q) (hU : U ∈ descendantsAtDepth Q j) :
    ∑ i : Fin 2, ∑ k : Fin 2,
      energy U (fun x => planarW1Derivative b x i k) ≤
        planarW1DerivativeFrobeniusLInf b ^ 2 := by
  let μ := normalizedCubeMeasure U
  let D := planarW1DerivativeFrobeniusLInf b
  have hD : 0 ≤ D := by dsimp [D, planarW1DerivativeFrobeniusLInf]; positivity
  have hbound : ∀ᵐ x ∂μ,
      ∑ i : Fin 2, ∑ k : Fin 2, planarW1Derivative b x i k ^ 2 ≤ D ^ 2 := by
    filter_upwards [ae_on_normalized_descendant Q U j hU
      (ae_planarW1Derivative_le_linf b)] with x hx
    have hnorm : planarFrobeniusNorm (planarW1Derivative b x) ^ 2 =
        ∑ i : Fin 2, ∑ k : Fin 2, planarW1Derivative b x i k ^ 2 := by
      unfold planarFrobeniusNorm
      exact Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun k _ => sq_nonneg _)
    rw [← hnorm]
    have hx' : planarFrobeniusNorm (planarW1Derivative b x) ≤ D := by
      simpa [D] using hx
    exact (sq_le_sq₀ (by unfold planarFrobeniusNorm; positivity) hD).2 hx'
  have hderiv : ∀ i k : Fin 2,
      MemLp (fun x => planarW1Derivative b x i k) 2 μ := by
    intro i k
    exact memLp_on_descendant_of_memLp hU
      ((b.component i).grad_memL2_normalizedCubeMeasure k)
  have hderivSqInt : ∀ i k : Fin 2,
      Integrable (fun x => planarW1Derivative b x i k ^ 2) μ := by
    intro i k
    have heq : (fun x => planarW1Derivative b x i k ^ 2) =
        (fun x => planarW1Derivative b x i k) *
          (fun x => planarW1Derivative b x i k) := by
      funext x
      simp only [pow_two, Pi.mul_apply]
    rw [heq]
    exact (hderiv i k).integrable_mul (hderiv i k)
  have hsumInt : Integrable
      (fun x => ∑ i : Fin 2, ∑ k : Fin 2,
        planarW1Derivative b x i k ^ 2) μ := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro k hk
    exact hderivSqInt i k
  calc
    ∑ i : Fin 2, ∑ k : Fin 2,
        energy U (fun x => planarW1Derivative b x i k) =
      ∫ x, ∑ i : Fin 2, ∑ k : Fin 2,
        planarW1Derivative b x i k ^ 2 ∂μ := by
          calc
            _ = ∑ i : Fin 2, ∑ k : Fin 2,
                ∫ x, planarW1Derivative b x i k ^ 2 ∂μ := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  apply Finset.sum_congr rfl
                  intro k hk
                  exact energy_eq_integral_sq U _
            _ = ∑ i : Fin 2, ∫ x, ∑ k : Fin 2,
                planarW1Derivative b x i k ^ 2 ∂μ := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact (integral_finsetSum Finset.univ
                    (fun k hk => hderivSqInt i k)).symm
            _ = ∫ x, ∑ i : Fin 2, ∑ k : Fin 2,
                planarW1Derivative b x i k ^ 2 ∂μ :=
                  (integral_finsetSum Finset.univ (fun i hi =>
                    integrable_finsetSum Finset.univ
                      (fun k hk => hderivSqInt i k))).symm
    _ ≤ ∫ _x, D ^ 2 ∂μ := integral_mono_ae hsumInt (integrable_const _) hbound
    _ = D ^ 2 := by
          rw [← cubeAverage_eq_integral_normalizedCubeMeasure, cubeAverage_const]
    _ = planarW1DerivativeFrobeniusLInf b ^ 2 := rfl

private theorem planarW1Value_oscillation_energy_le (Q U : TriadicCube 2) (j : ℕ)
    (b : PlanarW1Infinity Q) (hU : U ∈ descendantsAtDepth Q j) :
    ∑ i : Fin 2, energy U
        (fun x => planarW1Value b x i - cubeAverage U (fun x => planarW1Value b x i)) ≤
      (cubeScaleFactor U / Real.pi) ^ 2 *
        planarW1DerivativeFrobeniusLInf b ^ 2 := by
  have hcomponent : ∀ i : Fin 2,
      MemLp (fun x => planarW1Value b x i) 2 (normalizedCubeMeasure U) := by
    intro i
    exact memLp_on_descendant_of_memLp hU
      (b.component i).memL2_normalizedCubeMeasure
  have hgrad : ∀ i k : Fin 2,
      MemLp (fun x => planarW1Derivative b x i k) 2 (normalizedCubeMeasure U) := by
    intro i k
    exact memLp_on_descendant_of_memLp hU
      ((b.component i).grad_memL2_normalizedCubeMeasure k)
  have hw : ∀ i : Fin 2,
      HasWeakGradientOn (openCubeSet U) (planarW1Value b · i)
        (fun x k => planarW1Derivative b x i k) := by
    intro i
    have h := ((b.component i).restrictToOpenSubcube hU).hasWeakGradient
    simpa only [planarW1Value, planarW1Derivative,
      H1Function.restrictToOpenSubcube_toFun, H1Function.restrictToOpenSubcube_grad] using h
  have hcell : ∀ i : Fin 2,
      energy U (fun x => planarW1Value b x i -
        cubeAverage U (fun x => planarW1Value b x i)) ≤
        (cubeScaleFactor U / Real.pi) ^ 2 *
          ∑ k : Fin 2, energy U (fun x => planarW1Derivative b x i k) := by
    intro i
    exact cube_poincare U (hcomponent i) (hgrad i) (hw i)
  have hsum := planarW1Derivative_energy_le_linf_sq Q U j b hU
  calc
    ∑ i : Fin 2, energy U
        (fun x => planarW1Value b x i - cubeAverage U (fun x => planarW1Value b x i))
      ≤ ∑ i : Fin 2,
          (cubeScaleFactor U / Real.pi) ^ 2 *
            ∑ k : Fin 2, energy U (fun x => planarW1Derivative b x i k) :=
        Finset.sum_le_sum fun i hi => hcell i
    _ = (cubeScaleFactor U / Real.pi) ^ 2 *
          ∑ i : Fin 2, ∑ k : Fin 2,
            energy U (fun x => planarW1Derivative b x i k) := by rw [Finset.mul_sum]
    _ ≤ (cubeScaleFactor U / Real.pi) ^ 2 *
          planarW1DerivativeFrobeniusLInf b ^ 2 := by
        exact mul_le_mul_of_nonneg_left hsum (sq_nonneg _)

private theorem cubeProjection_mul_projected (Q : TriadicCube 2) (j : ℕ)
    {f g : Vec 2 → ℝ} :
    cubeProjection Q j (fun x => f x * cubeProjection Q j g x) =
      fun x => cubeProjection Q j f x * cubeProjection Q j g x := by
  funext x
  by_cases hx : x ∈ cubeSet Q
  · obtain ⟨U, hU, hxU⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet j hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hU hxU,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hU hxU,
      cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hU hxU]
    have hconst : ∀ y ∈ cubeSet U, cubeProjection Q j g y = cubeAverage U g := by
      intro y hy
      exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth g hU hy
    have hmean : cubeAverage U (fun y => f y * cubeProjection Q j g y) =
        cubeAverage U f * cubeAverage U g := by
      calc
        cubeAverage U (fun y => f y * cubeProjection Q j g y) =
            cubeAverage U (fun y => f y * cubeAverage U g) := by
              apply cubeAverage_congr_on_cubeSet
              intro y hy
              rw [hconst y hy]
        _ = cubeAverage U f * cubeAverage U g := by
              calc
                cubeAverage U (fun y => f y * cubeAverage U g) =
                    ∫ y, f y * cubeAverage U g ∂normalizedCubeMeasure U :=
                  cubeAverage_eq_integral_normalizedCubeMeasure U _
                _ = (∫ y, f y ∂normalizedCubeMeasure U) * cubeAverage U g :=
                  integral_mul_const (cubeAverage U g) f
                _ = cubeAverage U f * cubeAverage U g := by
                  rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
    rw [hmean]
  · rw [cubeProjection_eq_zero_of_not_mem_cubeSet Q j _ hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q j f hx,
      cubeProjection_eq_zero_of_not_mem_cubeSet Q j g hx,
      zero_mul]

private theorem energy_const_mul (Q : TriadicCube 2) (c : ℝ) (f : Vec 2 → ℝ) :
    energy Q (fun x => c * f x) = c ^ 2 * energy Q f := by
  rw [energy_eq_integral_sq Q, energy_eq_integral_sq Q]
  calc
    (∫ x, (c * f x) ^ 2 ∂normalizedCubeMeasure Q) =
        ∫ x, c ^ 2 * f x ^ 2 ∂normalizedCubeMeasure Q := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = c ^ 2 * ∫ x, f x ^ 2 ∂normalizedCubeMeasure Q := integral_const_mul _ _

private theorem vectorEnergy_projectedOscillation_le (Q : TriadicCube 2) (j : ℕ)
    (b : PlanarW1Infinity Q) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    ∑ i : Fin 2, energy Q (fun x =>
      (planarW1Value b x i - cubeProjection Q j (planarW1Value b · i) x) *
        cubeProjection Q j f x) ≤
      cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) *
        planarW1DerivativeFrobeniusLInf b ^ 2 * energy Q f := by
  have hDiff : ∀ i : Fin 2,
      MemLp (fun x => planarW1Value b x i -
        cubeProjection Q j (planarW1Value b · i) x) 2 (normalizedCubeMeasure Q) := by
    intro i
    exact (b.component i).memL2_normalizedCubeMeasure.sub
      (projection_memLp Q j (planarW1Value b · i) 2)
  have hProjTop : MemLp (cubeProjection Q j f) ⊤ (normalizedCubeMeasure Q) :=
    projection_memLp Q j f ⊤
  have hProduct : ∀ i : Fin 2,
      MemLp (fun x =>
        (planarW1Value b x i - cubeProjection Q j (planarW1Value b · i) x) *
          cubeProjection Q j f x) 2 (normalizedCubeMeasure Q) := by
    intro i
    exact (hDiff i).mul hProjTop
  have hcoord : ∀ i : Fin 2,
      energy Q (fun x =>
        (planarW1Value b x i - cubeProjection Q j (planarW1Value b · i) x) *
          cubeProjection Q j f x) =
      descendantsAverage Q j (fun U => (cubeAverage U f) ^ 2 *
        energy U (fun x => planarW1Value b x i - cubeAverage U (planarW1Value b · i))) := by
    intro i
    rw [energy_eq_descendantsAverage Q j (hProduct i)]
    unfold descendantsAverage
    apply congrArg (fun z : ℝ =>
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ * z)
    apply Finset.sum_congr rfl
    intro U hU
    have hbproj : ∀ x ∈ cubeSet U,
        cubeProjection Q j (planarW1Value b · i) x =
          cubeAverage U (planarW1Value b · i) := by
      intro x hx
      exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hU hx
    have hfproj : ∀ x ∈ cubeSet U, cubeProjection Q j f x = cubeAverage U f := by
      intro x hx
      exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hU hx
    calc
      energy U (fun x =>
        (planarW1Value b x i - cubeProjection Q j (planarW1Value b · i) x) *
          cubeProjection Q j f x) =
        energy U (fun x => cubeAverage U f *
          (planarW1Value b x i - cubeAverage U (planarW1Value b · i))) := by
            unfold energy pairing
            apply cubeAverage_congr_on_cubeSet
            intro x hx
            change
              ((planarW1Value b x i - cubeProjection Q j (planarW1Value b · i) x) *
                cubeProjection Q j f x) *
                ((planarW1Value b x i - cubeProjection Q j (planarW1Value b · i) x) *
                  cubeProjection Q j f x) =
              (cubeAverage U f *
                (planarW1Value b x i - cubeAverage U (planarW1Value b · i))) *
                (cubeAverage U f *
                  (planarW1Value b x i - cubeAverage U (planarW1Value b · i)))
            rw [hbproj x hx, hfproj x hx]
            ring
      _ = (cubeAverage U f) ^ 2 *
          energy U (fun x => planarW1Value b x i -
            cubeAverage U (planarW1Value b · i)) := by
            exact energy_const_mul U (cubeAverage U f) _
  have hsum :
      ∑ i : Fin 2, descendantsAverage Q j (fun U => (cubeAverage U f) ^ 2 *
        energy U (fun x => planarW1Value b x i - cubeAverage U (planarW1Value b · i))) =
      descendantsAverage Q j (fun U => (cubeAverage U f) ^ 2 *
        ∑ i : Fin 2, energy U (fun x => planarW1Value b x i -
          cubeAverage U (fun x => planarW1Value b x i))) := by
    rw [← descendantsAverage_sum (Q := Q) (j := j)
      (F := fun i U => (cubeAverage U f) ^ 2 *
        energy U (fun x => planarW1Value b x i - cubeAverage U (planarW1Value b · i)))]
    congr 1
    funext U
    rw [Finset.mul_sum]
  have hcellBound : ∀ U ∈ descendantsAtDepth Q j,
      (cubeAverage U f) ^ 2 *
        ∑ i : Fin 2, energy U (fun x => planarW1Value b x i -
          cubeAverage U (fun x => planarW1Value b x i)) ≤
      (cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) *
        planarW1DerivativeFrobeniusLInf b ^ 2) * (cubeAverage U f) ^ 2 := by
    intro U hU
    have hosc := planarW1Value_oscillation_energy_le Q U j b hU
    have hscale : (cubeScaleFactor U / Real.pi) ^ 2 =
        cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) := by
      rw [cubeScaleFactor_descendant_eq_div_pow hU]
      have h9 : ((3 : ℝ) ^ j) ^ 2 = (9 : ℝ) ^ j := by
        rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
        norm_num
      field_simp [Real.pi_ne_zero,
        pow_ne_zero j (by norm_num : (3 : ℝ) ≠ 0)]
      rw [h9]
    rw [hscale] at hosc
    calc
      (cubeAverage U f) ^ 2 *
          ∑ i : Fin 2, energy U (fun x => planarW1Value b x i -
            cubeAverage U (fun x => planarW1Value b x i)) ≤
        (cubeAverage U f) ^ 2 *
          (cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) *
            planarW1DerivativeFrobeniusLInf b ^ 2) :=
              mul_le_mul_of_nonneg_left hosc (sq_nonneg (cubeAverage U f))
      _ = (cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) *
            planarW1DerivativeFrobeniusLInf b ^ 2) * (cubeAverage U f) ^ 2 := by ring
  have hdesc :
      descendantsAverage Q j (fun U => (cubeAverage U f) ^ 2 *
        ∑ i : Fin 2, energy U (fun x => planarW1Value b x i -
          cubeAverage U (fun x => planarW1Value b x i))) ≤
      (cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) *
        planarW1DerivativeFrobeniusLInf b ^ 2) *
          descendantsAverage Q j (fun U => (cubeAverage U f) ^ 2) := by
    refine (descendantsAverage_le hcellBound).trans ?_
    rw [descendantsAverage_mul_left]
  have hmeanSquare : descendantsAverage Q j (fun U => (cubeAverage U f) ^ 2) =
      energy Q (cubeProjection Q j f) := by
    symm
    rw [energy_eq_descendantsAverage Q j (projection_memLp Q j f 2)]
    unfold descendantsAverage
    apply congrArg (fun z : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * z)
    apply Finset.sum_congr rfl
    intro U hU
    have hproj : ∀ x ∈ cubeSet U, cubeProjection Q j f x = cubeAverage U f := by
      intro x hx
      exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hU hx
    unfold energy pairing
    calc
      cubeAverage U (fun x => cubeProjection Q j f x * cubeProjection Q j f x) =
          cubeAverage U (fun _ => cubeAverage U f ^ 2) := by
            apply cubeAverage_congr_on_cubeSet
            intro x hx
            rw [hproj x hx]
            ring
      _ = cubeAverage U f ^ 2 := cubeAverage_const U _
  have hmean := energy_projection_le Q j hf
  calc
    ∑ i : Fin 2, energy Q (fun x =>
        (planarW1Value b x i - cubeProjection Q j (planarW1Value b · i) x) *
          cubeProjection Q j f x)
      = ∑ i : Fin 2, descendantsAverage Q j (fun U => (cubeAverage U f) ^ 2 *
          energy U (fun x => planarW1Value b x i -
            cubeAverage U (planarW1Value b · i))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hcoord i
    _ = descendantsAverage Q j (fun U => (cubeAverage U f) ^ 2 *
          ∑ i : Fin 2, energy U (fun x => planarW1Value b x i -
            cubeAverage U (fun x => planarW1Value b x i))) := hsum
    _ ≤ (cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) *
          planarW1DerivativeFrobeniusLInf b ^ 2) *
            energy Q (cubeProjection Q j f) := by
              rw [← hmeanSquare]
              exact hdesc
    _ ≤ (cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) *
          planarW1DerivativeFrobeniusLInf b ^ 2) * energy Q f := by
            exact mul_le_mul_of_nonneg_left hmean
              (mul_nonneg (div_nonneg (sq_nonneg _) (by positivity)) (sq_nonneg _))

private def planarVectorEnergy (Q : TriadicCube 2) (F : Vec 2 → Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, energy Q (fun x => F x i)

private def planarVectorPairing (Q : TriadicCube 2) (F G : Vec 2 → Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin 2, pairing Q (fun x => F x i) (fun x => G x i)

private theorem energy_add (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    energy Q (fun x => f x + g x) =
      energy Q f + 2 * pairing Q f g + energy Q g := by
  have hff : Integrable (fun x => f x ^ 2) (normalizedCubeMeasure Q) := by
    convert hf.integrable_mul hf using 1
    ext x
    simp only [pow_two, Pi.mul_apply]
  have hgg : Integrable (fun x => g x ^ 2) (normalizedCubeMeasure Q) := by
    convert hg.integrable_mul hg using 1
    ext x
    simp only [pow_two, Pi.mul_apply]
  have hfg : Integrable (fun x => f x * g x) (normalizedCubeMeasure Q) :=
    hf.integrable_mul hg
  have h2fg : Integrable (fun x => 2 * (f x * g x))
      (normalizedCubeMeasure Q) := by
    exact hfg.const_mul 2
  calc
    energy Q (fun x => f x + g x) =
        ∫ x, (f x + g x) ^ 2 ∂normalizedCubeMeasure Q :=
          energy_eq_integral_sq Q _
    _ = ∫ x, f x ^ 2 + 2 * (f x * g x) + g x ^ 2
          ∂normalizedCubeMeasure Q := by
            apply integral_congr_ae
            filter_upwards with x
            ring
    _ = (∫ x, f x ^ 2 ∂normalizedCubeMeasure Q) +
          ((∫ x, 2 * (f x * g x) ∂normalizedCubeMeasure Q) +
            ∫ x, g x ^ 2 ∂normalizedCubeMeasure Q) := by
            calc
              _ = (∫ x, f x ^ 2 + 2 * (f x * g x) ∂normalizedCubeMeasure Q) +
                    ∫ x, g x ^ 2 ∂normalizedCubeMeasure Q := by
                      simpa only [Pi.add_apply] using
                        (integral_add (hff.add h2fg) hgg)
              _ = (∫ x, f x ^ 2 ∂normalizedCubeMeasure Q) +
                    ((∫ x, 2 * (f x * g x) ∂normalizedCubeMeasure Q) +
                      ∫ x, g x ^ 2 ∂normalizedCubeMeasure Q) := by
                      rw [integral_add hff h2fg]
                      ring
    _ = energy Q f + 2 * pairing Q f g + energy Q g := by
          rw [energy_eq_integral_sq Q f, energy_eq_integral_sq Q g]
          rw [pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
          rw [integral_const_mul]
          ring

private theorem planarVectorEnergy_add (Q : TriadicCube 2)
    {F G : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    planarVectorEnergy Q (fun x i => F x i + G x i) =
      planarVectorEnergy Q F + 2 * planarVectorPairing Q F G + planarVectorEnergy Q G := by
  unfold planarVectorEnergy planarVectorPairing
  calc
    ∑ i : Fin 2, energy Q (fun x => F x i + G x i) =
        ∑ i : Fin 2,
          (energy Q (fun x => F x i) +
            2 * pairing Q (fun x => F x i) (fun x => G x i) +
            energy Q (fun x => G x i)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact energy_add Q (hF i) (hG i)
    _ = (∑ i : Fin 2, energy Q (fun x => F x i)) +
          2 * (∑ i : Fin 2, pairing Q (fun x => F x i) (fun x => G x i)) +
          ∑ i : Fin 2, energy Q (fun x => G x i) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem abs_planarVectorPairing_le (Q : TriadicCube 2)
    {F G : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    |planarVectorPairing Q F G| ≤
      Real.sqrt (planarVectorEnergy Q F) * Real.sqrt (planarVectorEnergy Q G) := by
  have hEF : 0 ≤ planarVectorEnergy Q F := by
    unfold planarVectorEnergy
    exact Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have hEG : 0 ≤ planarVectorEnergy Q G := by
    unfold planarVectorEnergy
    exact Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have hcoord : ∀ i : Fin 2,
      |pairing Q (fun x => F x i) (fun x => G x i)| ≤
        Real.sqrt (energy Q (fun x => F x i)) *
          Real.sqrt (energy Q (fun x => G x i)) := by
    intro i
    simpa [l2Norm] using abs_pairing_le Q (hF i) (hG i)
  have hsum :
      |planarVectorPairing Q F G| ≤
        ∑ i : Fin 2, Real.sqrt (energy Q (fun x => F x i)) *
          Real.sqrt (energy Q (fun x => G x i)) := by
    unfold planarVectorPairing
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => hcoord i)
  have hcs :
      (∑ i : Fin 2, Real.sqrt (energy Q (fun x => F x i)) *
        Real.sqrt (energy Q (fun x => G x i))) ^ 2 ≤
      planarVectorEnergy Q F * planarVectorEnergy Q G := by
    unfold planarVectorEnergy
    calc
      _ ≤ (∑ i : Fin 2, Real.sqrt (energy Q (fun x => F x i)) ^ 2) *
            ∑ i : Fin 2, Real.sqrt (energy Q (fun x => G x i)) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ = (∑ i : Fin 2, energy Q (fun x => F x i)) *
            ∑ i : Fin 2, energy Q (fun x => G x i) := by
              congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
                rw [Real.sq_sqrt (energy_nonneg Q _)]
  have hprod : 0 ≤ Real.sqrt (planarVectorEnergy Q F) *
      Real.sqrt (planarVectorEnergy Q G) := by positivity
  have hprodSq : (Real.sqrt (planarVectorEnergy Q F) *
      Real.sqrt (planarVectorEnergy Q G)) ^ 2 =
        planarVectorEnergy Q F * planarVectorEnergy Q G := by
    rw [mul_pow, Real.sq_sqrt hEF, Real.sq_sqrt hEG]
  apply (sq_le_sq₀ (abs_nonneg _) hprod).mp
  calc
    |planarVectorPairing Q F G| ^ 2 ≤
        (∑ i : Fin 2, Real.sqrt (energy Q (fun x => F x i)) *
          Real.sqrt (energy Q (fun x => G x i))) ^ 2 := by
            exact (sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg fun i _ =>
              mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hsum
    _ ≤ planarVectorEnergy Q F * planarVectorEnergy Q G := hcs
    _ = (Real.sqrt (planarVectorEnergy Q F) *
          Real.sqrt (planarVectorEnergy Q G)) ^ 2 := hprodSq.symm

private theorem sqrt_planarVectorEnergy_add_le (Q : TriadicCube 2)
    {F G : Vec 2 → Fin 2 → ℝ}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    Real.sqrt (planarVectorEnergy Q (fun x i => F x i + G x i)) ≤
      Real.sqrt (planarVectorEnergy Q F) + Real.sqrt (planarVectorEnergy Q G) := by
  have hFnonneg : 0 ≤ planarVectorEnergy Q F := by
    unfold planarVectorEnergy
    exact Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have hGnonneg : 0 ≤ planarVectorEnergy Q G := by
    unfold planarVectorEnergy
    exact Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have hcross := abs_planarVectorPairing_le Q hF hG
  have henergy := planarVectorEnergy_add Q hF hG
  have hbound : planarVectorEnergy Q (fun x i => F x i + G x i) ≤
      (Real.sqrt (planarVectorEnergy Q F) +
        Real.sqrt (planarVectorEnergy Q G)) ^ 2 := by
    rw [henergy]
    have hpair : planarVectorPairing Q F G ≤
        Real.sqrt (planarVectorEnergy Q F) * Real.sqrt (planarVectorEnergy Q G) :=
      (le_abs_self _).trans hcross
    have hsF : 0 ≤ Real.sqrt (planarVectorEnergy Q F) := Real.sqrt_nonneg _
    have hsG : 0 ≤ Real.sqrt (planarVectorEnergy Q G) := Real.sqrt_nonneg _
    nlinarith only [hpair, hsF, hsG, Real.sq_sqrt hFnonneg,
      Real.sq_sqrt hGnonneg]
  calc
    Real.sqrt (planarVectorEnergy Q (fun x i => F x i + G x i)) ≤
        Real.sqrt ((Real.sqrt (planarVectorEnergy Q F) +
          Real.sqrt (planarVectorEnergy Q G)) ^ 2) := Real.sqrt_le_sqrt hbound
    _ = Real.sqrt (planarVectorEnergy Q F) +
        Real.sqrt (planarVectorEnergy Q G) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]

private theorem vector_product_residual_sqrt_le (Q : TriadicCube 2)
    (b : PlanarW1Infinity Q) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (j : ℕ) :
    Real.sqrt (planarVectorEnergy Q (fun x i =>
      planarW1Value b x i * f x -
        cubeProjection Q j (fun y => planarW1Value b y i * f y) x)) ≤
      planarW1ValueLInf b * Real.sqrt (energy Q (fun x => f x - cubeProjection Q j f x)) +
        (cubeScaleFactor Q / ((3 : ℝ) ^ j * Real.pi)) *
          planarW1DerivativeFrobeniusLInf b * Real.sqrt (energy Q f) := by
  let μ := normalizedCubeMeasure Q
  let A : Vec 2 → Fin 2 → ℝ := fun x i =>
    planarW1Value b x i * (f x - cubeProjection Q j f x) -
      cubeProjection Q j (fun y => planarW1Value b y i *
        (f y - cubeProjection Q j f y)) x
  let B : Vec 2 → Fin 2 → ℝ := fun x i =>
    (planarW1Value b x i - cubeProjection Q j (planarW1Value b · i) x) *
      cubeProjection Q j f x
  have hprojf : MemLp (cubeProjection Q j f) 2 μ := projection_memLp Q j f 2
  have hres : MemLp (fun x => f x - cubeProjection Q j f x) 2 μ := hf.sub hprojf
  have hprod : ∀ i : Fin 2, MemLp (fun x => planarW1Value b x i * f x) 2 μ := by
    intro i
    exact (b.component_memLp_top i).mul hf
  have hprodA : ∀ i : Fin 2,
      MemLp (fun x => planarW1Value b x i *
        (f x - cubeProjection Q j f x)) 2 μ := by
    intro i
    exact (b.component_memLp_top i).mul hres
  have hprodB : ∀ i : Fin 2,
      MemLp (fun x => planarW1Value b x i * cubeProjection Q j f x) 2 μ := by
    intro i
    exact (b.component_memLp_top i).mul hprojf
  have hsplit : ∀ i : Fin 2,
      (fun x => planarW1Value b x i * f x) =
        (fun x => planarW1Value b x i *
          (f x - cubeProjection Q j f x)) +
        (fun x => planarW1Value b x i * cubeProjection Q j f x) := by
    intro i
    funext x
    simp only [Pi.add_apply]
    ring
  have hdecomp : ∀ i : Fin 2,
      (fun x => planarW1Value b x i * f x -
        cubeProjection Q j (fun y => planarW1Value b y i * f y) x) =
      (fun x => A x i + B x i) := by
    intro i
    have hprojection := projection_add Q j (hprodA i) (hprodB i)
    have hmulproj := cubeProjection_mul_projected Q j
      (f := fun x => planarW1Value b x i) (g := f)
    have hsplitProjection := congrArg (cubeProjection Q j) (hsplit i)
    funext x
    rw [congrFun (hsplit i) x, congrFun hsplitProjection x]
    change ((fun y => planarW1Value b y i *
        (f y - cubeProjection Q j f y)) x +
      (fun y => planarW1Value b y i * cubeProjection Q j f y) x) -
        cubeProjection Q j
          ((fun y => planarW1Value b y i *
              (f y - cubeProjection Q j f y)) +
            (fun y => planarW1Value b y i * cubeProjection Q j f y)) x =
      A x i + B x i
    rw [Pi.add_def]
    rw [congrFun hprojection x]
    rw [congrFun hmulproj x]
    dsimp [A, B]
    ring
  have hAMem : ∀ i : Fin 2, MemLp (fun x => A x i) 2 μ := by
    intro i
    dsimp [A]
    exact (hprodA i).sub (projection_memLp Q j _ 2)
  have hBMem : ∀ i : Fin 2, MemLp (fun x => B x i) 2 μ := by
    intro i
    dsimp [B]
    have hb : MemLp (fun x => planarW1Value b x i -
        cubeProjection Q j (planarW1Value b · i) x) 2 μ :=
      (b.component i).memL2_normalizedCubeMeasure.sub
        (projection_memLp Q j (planarW1Value b · i) 2)
    exact hb.mul (projection_memLp Q j f ⊤)
  have hAenergy : planarVectorEnergy Q A ≤
      planarW1ValueLInf b ^ 2 * energy Q (fun x => f x - cubeProjection Q j f x) := by
    calc
      planarVectorEnergy Q A ≤
          ∑ i : Fin 2, energy Q (fun x => planarW1Value b x i *
            (f x - cubeProjection Q j f x)) := by
              unfold planarVectorEnergy
              apply Finset.sum_le_sum
              intro i hi
              rw [show (fun x => A x i) =
                (fun x => planarW1Value b x i *
                  (f x - cubeProjection Q j f x) -
                    cubeProjection Q j (fun y => planarW1Value b y i *
                      (f y - cubeProjection Q j f y)) x) by rfl]
              rw [energy_residual Q j (hprodA i)]
              exact sub_le_self _ (energy_nonneg Q _)
      _ ≤ planarW1ValueLInf b ^ 2 *
          energy Q (fun x => f x - cubeProjection Q j f x) :=
            vectorEnergy_mul_le_linf Q b hres
  have hBenergy : planarVectorEnergy Q B ≤
      cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) *
        planarW1DerivativeFrobeniusLInf b ^ 2 * energy Q f := by
    simpa [B, planarVectorEnergy, mul_comm, mul_left_comm, mul_assoc] using
      vectorEnergy_projectedOscillation_le Q j b hf
  have hM : 0 ≤ planarW1ValueLInf b := by
    dsimp [planarW1ValueLInf]
    positivity
  have hD : 0 ≤ planarW1DerivativeFrobeniusLInf b := by
    dsimp [planarW1DerivativeFrobeniusLInf]
    positivity
  have hEres : 0 ≤ energy Q (fun x => f x - cubeProjection Q j f x) := energy_nonneg Q _
  have hEf : 0 ≤ energy Q f := energy_nonneg Q f
  have hAroot : Real.sqrt (planarVectorEnergy Q A) ≤
      planarW1ValueLInf b * Real.sqrt (energy Q (fun x => f x - cubeProjection Q j f x)) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg hM (Real.sqrt_nonneg _), ?_⟩
    calc
      planarVectorEnergy Q A ≤
          planarW1ValueLInf b ^ 2 * energy Q (fun x => f x - cubeProjection Q j f x) := hAenergy
      _ = (planarW1ValueLInf b *
          Real.sqrt (energy Q (fun x => f x - cubeProjection Q j f x))) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hEres]
  have hBroot : Real.sqrt (planarVectorEnergy Q B) ≤
      (cubeScaleFactor Q / ((3 : ℝ) ^ j * Real.pi)) *
        planarW1DerivativeFrobeniusLInf b * Real.sqrt (energy Q f) := by
    let C : ℝ := cubeScaleFactor Q / ((3 : ℝ) ^ j * Real.pi)
    have hC : 0 ≤ C := by
      dsimp [C]
      exact div_nonneg (cubeScaleFactor_pos' Q).le
        (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) Real.pi_pos.le)
    have hcoeff : cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) = C ^ 2 := by
      dsimp [C]
      have hpow : ((3 : ℝ) ^ j) ^ 2 = (9 : ℝ) ^ j := by
        rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
        norm_num
      rw [div_pow, mul_pow, hpow]
    apply (Real.sqrt_le_iff).2
    refine ⟨mul_nonneg (mul_nonneg hC hD) (Real.sqrt_nonneg _), ?_⟩
    calc
      planarVectorEnergy Q B ≤
          cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) *
            planarW1DerivativeFrobeniusLInf b ^ 2 * energy Q f := hBenergy
      _ = (C * planarW1DerivativeFrobeniusLInf b * Real.sqrt (energy Q f)) ^ 2 := by
            rw [hcoeff, mul_pow, Real.sq_sqrt hEf]
            ring
  have hdecompVector :
      (fun x i => planarW1Value b x i * f x -
        cubeProjection Q j (fun y => planarW1Value b y i * f y) x) =
      (fun x i => A x i + B x i) := by
    funext x i
    exact congrFun (hdecomp i) x
  rw [hdecompVector]
  calc
    Real.sqrt (planarVectorEnergy Q (fun x i => A x i + B x i)) ≤
        Real.sqrt (planarVectorEnergy Q A) + Real.sqrt (planarVectorEnergy Q B) :=
      sqrt_planarVectorEnergy_add_le Q hAMem hBMem
    _ ≤ planarW1ValueLInf b *
          Real.sqrt (energy Q (fun x => f x - cubeProjection Q j f x)) +
        (cubeScaleFactor Q / ((3 : ℝ) ^ j * Real.pi)) *
          planarW1DerivativeFrobeniusLInf b * Real.sqrt (energy Q f) :=
      add_le_add hAroot hBroot

private theorem sqrt_tsum_sq_add_le (a b : ℕ → ℝ)
    (ha : Summable (fun n => a n ^ 2)) (hb : Summable (fun n => b n ^ 2)) :
    Real.sqrt (∑' n, (a n + b n) ^ 2) ≤
      Real.sqrt (∑' n, a n ^ 2) + Real.sqrt (∑' n, b n ^ 2) := by
  have hmem (c : ℕ → ℝ) (hc : Summable (fun n => c n ^ 2)) : Memℓp c (2 : ℝ≥0∞) := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    simpa [Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using hc
  let A : lp (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) := ⟨a, hmem a ha⟩
  let B : lp (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) := ⟨b, hmem b hb⟩
  have hA : ‖A‖ ^ 2 = ∑' n, a n ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) A
    simpa [A, Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using h
  have hB : ‖B‖ ^ 2 = ∑' n, b n ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) B
    simpa [B, Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using h
  have hAB : ‖A + B‖ ^ 2 = ∑' n, (a n + b n) ^ 2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (A + B)
    have h' : ‖A + B‖ ^ 2 = ∑' n, ‖(A + B) n‖ ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs, ENNReal.toReal_ofNat] using h
    calc
      ‖A + B‖ ^ 2 = ∑' n, ‖(A + B) n‖ ^ 2 := h'
      _ = ∑' n, (a n + b n) ^ 2 := by
        apply tsum_congr
        intro n
        rw [lp.coeFn_add]
        change ‖(a n + b n)‖ ^ 2 = (a n + b n) ^ 2
        simp [Real.norm_eq_abs, sq_abs]
  have hnorm := norm_add_le A B
  have hAn : 0 ≤ ‖A‖ := norm_nonneg _
  have hBn : 0 ≤ ‖B‖ := norm_nonneg _
  have hABn : 0 ≤ ‖A + B‖ := norm_nonneg _
  calc
    Real.sqrt (∑' n, (a n + b n) ^ 2) = ‖A + B‖ := by
      rw [← hAB, Real.sqrt_sq_eq_abs, abs_of_nonneg hABn]
    _ ≤ ‖A‖ + ‖B‖ := hnorm
    _ = Real.sqrt (∑' n, a n ^ 2) + Real.sqrt (∑' n, b n ^ 2) := by
      rw [← hA, ← hB, Real.sqrt_sq_eq_abs, abs_of_nonneg hAn,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hBn]

/-- The order-`1/4` positive-Haar multiplier estimate for a planar vector
field with weak `W^{1,∞}` data and a scalar `H¹` input. The residual series
converges by the positive-Haar increment theorem; its sharp constant follows
from the direct-sum Minkowski inequality across all Haar depths. -/
theorem vectorPositiveHaarNorm_mul_le (Q : TriadicCube 2)
    (b : PlanarW1Infinity Q) (f : H1Function (openCubeSet Q)) :
    vectorPositiveHaarNorm Q (fun x i => planarW1Value b x i * f.toFun x) ≤
      planarW1ValueLInf b * positiveHaarNorm Q f.toFun +
        cubeScaleFactor Q * planarC1 * planarW1DerivativeFrobeniusLInf b *
          Real.sqrt (energy Q f.toFun) := by
  let q : ℝ := Real.sqrt 3
  let δ : ℝ := q - 1
  let R : ℝ := cubeScaleFactor Q
  let M : ℝ := planarW1ValueLInf b
  let D : ℝ := planarW1DerivativeFrobeniusLInf b
  let E : ℝ := energy Q f.toFun
  let F : Vec 2 → Fin 2 → ℝ := fun x i => planarW1Value b x i * f.toFun x
  let Fres : ℕ → Vec 2 → Fin 2 → ℝ := fun j x i =>
    F x i - cubeProjection Q j (fun y => F y i) x
  let α : ℕ → ℝ := fun j => Real.sqrt (δ * q ^ j)
  let β : ℕ → ℝ := fun j => (R / ((3 : ℝ) ^ j * Real.pi)) * D * Real.sqrt E
  let a : ℕ → ℝ := fun n => Nat.casesOn n
    (M * Real.sqrt E) (fun j => α j * (M * Real.sqrt
      (energy Q (fun x => f.toFun x - cubeProjection Q j f.toFun x))))
  let bseq : ℕ → ℝ := fun n => Nat.casesOn n 0 (fun j => α j * β j)
  let c : ℕ → ℝ := fun n => Nat.casesOn n
    (Real.sqrt (planarVectorEnergy Q F))
    (fun j => α j * Real.sqrt (planarVectorEnergy Q (Fres j)))
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hqgt : 1 < q := by
    dsimp [q]
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδnonneg : 0 ≤ δ := hδ.le
  have hq9 : q / 9 < 1 := by
    dsimp [q]
    nlinarith [Real.sqrt_nonneg (3 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hR : 0 < R := by dsimp [R]; exact cubeScaleFactor_pos' Q
  have hM : 0 ≤ M := by dsimp [M, planarW1ValueLInf]; positivity
  have hD : 0 ≤ D := by dsimp [D, planarW1DerivativeFrobeniusLInf]; positivity
  have hE : 0 ≤ E := by dsimp [E]; exact energy_nonneg Q f.toFun
  have hf : MemLp f.toFun 2 (normalizedCubeMeasure Q) :=
    f.memL2_normalizedCubeMeasure
  have hG : ∀ i : Fin 2, MemLp (fun x => f.grad x i) 2
      (normalizedCubeMeasure Q) := f.grad_memL2_normalizedCubeMeasure
  have hpos : Summable (fun j : ℕ => q ^ j *
      energy Q (fun x => f.toFun x - cubeProjection Q j f.toFun x)) := by
    simpa only [q] using positiveHaarResidualSeries_summable Q hf hG f.hasWeakGradient
  have hFmem : ∀ i : Fin 2, MemLp (fun x => F x i) 2
      (normalizedCubeMeasure Q) := by
    intro i
    dsimp [F]
    exact (b.component_memLp_top i).mul hf
  have hresVecNonneg : ∀ j, 0 ≤ planarVectorEnergy Q (Fres j) := by
    intro j
    unfold planarVectorEnergy
    exact Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have hEresNonneg : ∀ j, 0 ≤ energy Q
      (fun x => f.toFun x - cubeProjection Q j f.toFun x) := by
    intro j
    exact energy_nonneg Q _
  have hrootBound : Real.sqrt (planarVectorEnergy Q F) ≤ M * Real.sqrt E := by
    have hmul := vectorEnergy_mul_le_linf Q b hf
    apply (Real.sqrt_le_iff).2
    refine ⟨?_, ?_⟩
    · positivity
    · calc
        planarVectorEnergy Q F ≤
            planarW1ValueLInf b ^ 2 * energy Q f.toFun := hmul
        _ = (planarW1ValueLInf b * Real.sqrt (energy Q f.toFun)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (energy_nonneg Q f.toFun)]
  have hroot : c 0 ≤ a 0 + bseq 0 := by
    simpa [a, bseq, c, F, M, E] using hrootBound
  have htail : ∀ j, c (j + 1) ≤ a (j + 1) + bseq (j + 1) := by
    intro j
    have hlocal := vector_product_residual_sqrt_le Q b hf j
    have hweighted := mul_le_mul_of_nonneg_left hlocal (Real.sqrt_nonneg (δ * q ^ j))
    simpa [a, bseq, c, α, β, Fres, F, M, D, E, R, q, δ,
      mul_add, mul_assoc, mul_left_comm, mul_comm] using hweighted
  have hpoint : ∀ n, c n ≤ a n + bseq n := by
    intro n
    cases n with
    | zero => exact hroot
    | succ j => exact htail j
  have hnonneg : ∀ n, 0 ≤ a n ∧ 0 ≤ bseq n ∧ 0 ≤ c n := by
    intro n
    cases n with
    | zero =>
        change 0 ≤ M * Real.sqrt E ∧ 0 ≤ (0 : ℝ) ∧
          0 ≤ Real.sqrt (planarVectorEnergy Q F)
        exact ⟨mul_nonneg hM (Real.sqrt_nonneg _), le_rfl, Real.sqrt_nonneg _⟩
    | succ j =>
        dsimp [a, bseq, c]
        have hα : 0 ≤ α j := Real.sqrt_nonneg _
        exact ⟨mul_nonneg hα (mul_nonneg hM (Real.sqrt_nonneg _)),
          mul_nonneg hα (by dsimp [β]; positivity),
          mul_nonneg hα (Real.sqrt_nonneg _)⟩
  have haTail : Summable (fun j => a (j + 1) ^ 2) := by
    refine (hpos.mul_left (δ * M ^ 2)).congr ?_
    intro j
    have hcoeff : 0 ≤ δ * q ^ j := mul_nonneg hδnonneg (pow_nonneg hqpos.le _)
    rw [show a (j + 1) = α j * (M * Real.sqrt
        (energy Q (fun x => f.toFun x - cubeProjection Q j f.toFun x))) by rfl,
      mul_pow, Real.sq_sqrt hcoeff, mul_pow, Real.sq_sqrt (hEresNonneg j)]
    ring
  have ha : Summable (fun n => a n ^ 2) :=
    (summable_nat_add_iff 1).1 haTail
  let C : ℝ := δ * (R ^ 2 / Real.pi ^ 2) * D ^ 2 * E
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgeom : Summable (fun j : ℕ => C * (q / 9) ^ j) :=
    (summable_geometric_of_lt_one (by positivity) hq9).mul_left C
  have hbetaSq : ∀ j, bseq (j + 1) ^ 2 = C * (q / 9) ^ j := by
    intro j
    have hpow : ((3 : ℝ) ^ j) ^ 2 = (9 : ℝ) ^ j := by
      rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
      norm_num
    have hcoeff : 0 ≤ δ * q ^ j := mul_nonneg hδnonneg (pow_nonneg hqpos.le _)
    have hβ : β j ^ 2 = R ^ 2 / (9 ^ j * Real.pi ^ 2) * D ^ 2 * E := by
      dsimp [β]
      rw [mul_pow, mul_pow, div_pow, mul_pow, Real.sq_sqrt hE, hpow]
    calc
      bseq (j + 1) ^ 2 =
          (Real.sqrt (δ * q ^ j) *
            ((R / ((3 : ℝ) ^ j * Real.pi)) * D * Real.sqrt E)) ^ 2 := by
              rfl
      _ = C * (q / 9) ^ j := by
            rw [mul_pow, Real.sq_sqrt hcoeff, hβ]
            dsimp [C]
            rw [div_pow]
            field_simp [Real.pi_ne_zero,
              pow_ne_zero j (by norm_num : (9 : ℝ) ≠ 0)]
  have hbTail : Summable (fun j => bseq (j + 1) ^ 2) := by
    refine hgeom.congr ?_
    intro j
    exact (hbetaSq j).symm
  have hb : Summable (fun n => bseq n ^ 2) :=
    (summable_nat_add_iff 1).1 hbTail
  have hadd : Summable (fun n => (a n + bseq n) ^ 2) := by
    have hmajor : Summable (fun n => 2 * a n ^ 2 + 2 * bseq n ^ 2) :=
      (ha.mul_left 2).add (hb.mul_left 2)
    apply hmajor.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (a n - bseq n)]
  have hc : Summable (fun n => c n ^ 2) := by
    apply hadd.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsumNonneg : 0 ≤ a n + bseq n := add_nonneg (hnonneg n).1 (hnonneg n).2.1
    exact (sq_le_sq₀ (hnonneg n).2.2 hsumNonneg).2 (hpoint n)
  have hcTail : Summable (fun j => c (j + 1) ^ 2) :=
    (summable_nat_add_iff 1).2 hc
  have hctailEq : ∀ j, c (j + 1) ^ 2 = δ * q ^ j *
      planarVectorEnergy Q (Fres j) := by
    intro j
    have hcoeff : 0 ≤ δ * q ^ j := mul_nonneg hδnonneg (pow_nonneg hqpos.le _)
    rw [show c (j + 1) = α j *
        Real.sqrt (planarVectorEnergy Q (Fres j)) by rfl,
      mul_pow, Real.sq_sqrt hcoeff, Real.sq_sqrt (hresVecNonneg j)]
  have hvecResSummable : Summable (fun j => q ^ j *
      planarVectorEnergy Q (Fres j)) := by
    refine (hcTail.mul_left δ⁻¹).congr ?_
    intro j
    rw [hctailEq j]
    have hδne : δ ≠ 0 := ne_of_gt hδ
    field_simp
  have hprodCoordPos : ∀ i : Fin 2, Summable (fun j => q ^ j *
      energy Q (fun x => F x i - cubeProjection Q j (fun y => F y i) x)) := by
    intro i
    apply hvecResSummable.of_norm_bounded
    intro j
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (pow_nonneg hqpos.le _) (energy_nonneg Q _))]
    have hcoord : energy Q (fun x => F x i - cubeProjection Q j (fun y => F y i) x) ≤
        planarVectorEnergy Q (Fres j) := by
      change energy Q (fun x => F x i - cubeProjection Q j (fun y => F y i) x) ≤
        ∑ k : Fin 2, energy Q
          (fun x => F x k - cubeProjection Q j (fun y => F y k) x)
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun k : Fin 2 => energy Q
          (fun x => F x k - cubeProjection Q j (fun y => F y k) x))
        (fun k hk => energy_nonneg Q _) (Finset.mem_univ i)
    exact mul_le_mul_of_nonneg_left hcoord (pow_nonneg hqpos.le _)
  have habel : ∀ i : Fin 2,
      primalEnergy Q q (fun x => F x i) = energy Q (fun x => F x i) +
        δ * ∑' j, q ^ j *
          energy Q (fun x => F x i - cubeProjection Q j (fun y => F y i) x) := by
    intro i
    have h := primalEnergy_eq_abel Q hqgt (hFmem i) (hprodCoordPos i)
    simpa [q, δ] using h
  have hcoordsTsum :
      (∑' j, q ^ j * energy Q (fun x => F x 0 -
        cubeProjection Q j (fun y => F y 0) x)) +
      (∑' j, q ^ j * energy Q (fun x => F x 1 -
        cubeProjection Q j (fun y => F y 1) x)) =
      ∑' j, q ^ j * planarVectorEnergy Q (Fres j) := by
    rw [← (hprodCoordPos 0).tsum_add (hprodCoordPos 1)]
    apply tsum_congr
    intro j
    unfold planarVectorEnergy Fres
    simp only [Fin.sum_univ_two]
    ring
  have hctsum : ∑' n, c n ^ 2 = planarVectorEnergy Q F +
      δ * ∑' j, q ^ j * planarVectorEnergy Q (Fres j) := by
    have hsplit := hc.sum_add_tsum_nat_add 1
    have htailTsum : ∑' j, c (j + 1) ^ 2 =
        δ * ∑' j, q ^ j * planarVectorEnergy Q (Fres j) := by
      rw [show (fun j => c (j + 1) ^ 2) =
        (fun j => δ * (q ^ j * planarVectorEnergy Q (Fres j))) by
          funext j
          rw [hctailEq j]
          ring, tsum_mul_left]
    calc
      ∑' n, c n ^ 2 = c 0 ^ 2 + ∑' j, c (j + 1) ^ 2 := by
        simpa only [Finset.sum_range_one] using hsplit.symm
      _ = planarVectorEnergy Q F +
          δ * ∑' j, q ^ j * planarVectorEnergy Q (Fres j) := by
            rw [htailTsum]
            have hcsq0 : c 0 ^ 2 = planarVectorEnergy Q F := by
              change (Real.sqrt (planarVectorEnergy Q F)) ^ 2 = _
              exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => energy_nonneg Q _)
            rw [hcsq0]
  have hproductEnergy : vectorPositiveHaarEnergy Q F = ∑' n, c n ^ 2 := by
    have hscalar0 : MemLp (fun x => F x 0) 2 (normalizedCubeMeasure Q) := hFmem 0
    have hscalar1 : MemLp (fun x => F x 1) 2 (normalizedCubeMeasure Q) := hFmem 1
    unfold vectorPositiveHaarEnergy
    rw [Fin.sum_univ_two, habel 0, habel 1]
    calc
      (energy Q (fun x => F x 0) +
          δ * ∑' j, q ^ j * energy Q (fun x => F x 0 -
            cubeProjection Q j (fun y => F y 0) x)) +
        (energy Q (fun x => F x 1) +
          δ * ∑' j, q ^ j * energy Q (fun x => F x 1 -
            cubeProjection Q j (fun y => F y 1) x)) =
        planarVectorEnergy Q F +
          δ * ∑' j, q ^ j * planarVectorEnergy Q (Fres j) := by
              rw [← hcoordsTsum]
              unfold planarVectorEnergy
              rw [Fin.sum_univ_two]
              ring
      _ = ∑' n, c n ^ 2 := hctsum.symm
  have hAtsum : ∑' n, a n ^ 2 = M ^ 2 * primalEnergy Q q f.toFun := by
    have hsplit := ha.sum_add_tsum_nat_add 1
    have htailTsum : ∑' j, a (j + 1) ^ 2 = δ * M ^ 2 * ∑' j, q ^ j *
        energy Q (fun x => f.toFun x - cubeProjection Q j f.toFun x) := by
      rw [show (fun j => a (j + 1) ^ 2) = (fun j =>
        (δ * M ^ 2) * (q ^ j * energy Q
          (fun x => f.toFun x - cubeProjection Q j f.toFun x))) by
          funext j
          have hcoeff : 0 ≤ δ * q ^ j := mul_nonneg hδnonneg (pow_nonneg hqpos.le _)
          rw [show a (j + 1) = α j * (M * Real.sqrt
            (energy Q (fun x => f.toFun x - cubeProjection Q j f.toFun x))) by rfl,
            mul_pow, Real.sq_sqrt hcoeff, mul_pow,
            Real.sq_sqrt (hEresNonneg j)]
          ring, tsum_mul_left]
    have habelF := primalEnergy_eq_abel Q hqgt hf hpos
    have ha0 : a 0 ^ 2 = M ^ 2 * E := by
      change (M * Real.sqrt E) ^ 2 = M ^ 2 * E
      rw [mul_pow, Real.sq_sqrt hE]
    calc
      ∑' n, a n ^ 2 = a 0 ^ 2 + ∑' j, a (j + 1) ^ 2 := by
        simpa only [Finset.sum_range_one] using hsplit.symm
      _ = M ^ 2 * E + δ * M ^ 2 * ∑' j, q ^ j *
          energy Q (fun x => f.toFun x - cubeProjection Q j f.toFun x) := by
            rw [ha0, htailTsum]
      _ = M ^ 2 * primalEnergy Q q f.toFun := by
            calc
              _ = M ^ 2 * (E + δ * ∑' j, q ^ j *
                    energy Q (fun x => f.toFun x - cubeProjection Q j f.toFun x)) := by
                      ring
              _ = M ^ 2 * primalEnergy Q q f.toFun := by
                    rw [← habelF]
  have hPnorm : positiveHaarNorm Q f.toFun ^ 2 = primalEnergy Q q f.toFun := by
    dsimp [positiveHaarNorm, q]
    exact Real.sq_sqrt
      (primalEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) f.toFun)
  have hAroot : Real.sqrt (∑' n, a n ^ 2) =
      M * positiveHaarNorm Q f.toFun := by
    have hsq : ∑' n, a n ^ 2 = (M * positiveHaarNorm Q f.toFun) ^ 2 := by
      rw [hAtsum, ← hPnorm]
      ring
    have hPnonneg : 0 ≤ positiveHaarNorm Q f.toFun := by
      dsimp [positiveHaarNorm]
      positivity
    rw [hsq, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hM hPnonneg)]
  have hBtsum : ∑' n, bseq n ^ 2 =
      (R * planarC1 * D * Real.sqrt E) ^ 2 := by
    have hsplit := hb.sum_add_tsum_nat_add 1
    have htailTsum : ∑' j, bseq (j + 1) ^ 2 = C * (1 - q / 9)⁻¹ := by
      rw [show (fun j => bseq (j + 1) ^ 2) =
        (fun j => C * (q / 9) ^ j) by
          funext j
          exact hbetaSq j, tsum_mul_left,
        tsum_geometric_of_lt_one (by positivity) hq9]
    have hc1 : planarC1 ^ 2 = δ / (Real.pi ^ 2 * (1 - q / 9)) := by
      simpa [q, δ] using planarC1_sq
    calc
      ∑' n, bseq n ^ 2 = bseq 0 ^ 2 + ∑' j, bseq (j + 1) ^ 2 := by
        simpa only [Finset.sum_range_one] using hsplit.symm
      _ = C * (1 - q / 9)⁻¹ := by
            rw [htailTsum]
            simp [bseq]
      _ = (R * planarC1 * D * Real.sqrt E) ^ 2 := by
            calc
              C * (1 - q / 9)⁻¹ =
                  R ^ 2 * (δ / (Real.pi ^ 2 * (1 - q / 9))) * D ^ 2 * E := by
                    dsimp [C]
                    field_simp [Real.pi_ne_zero]
              _ = R ^ 2 * planarC1 ^ 2 * D ^ 2 * E := by rw [← hc1]
              _ = (R * planarC1 * D * Real.sqrt E) ^ 2 := by
                    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hE]
  have hBroot : Real.sqrt (∑' n, bseq n ^ 2) =
      R * planarC1 * D * Real.sqrt E := by
    have hc1nonneg : 0 ≤ planarC1 := by dsimp [planarC1]; positivity
    have hcoefNonneg : 0 ≤ R * planarC1 * D :=
      mul_nonneg (mul_nonneg hR.le hc1nonneg) hD
    rw [hBtsum, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hcoefNonneg (Real.sqrt_nonneg E))]
  have hsumle : (∑' n, c n ^ 2) ≤ ∑' n, (a n + bseq n) ^ 2 := by
    apply hc.tsum_le_tsum ?_ hadd
    intro n
    exact (sq_le_sq₀ (hnonneg n).2.2
      (add_nonneg (hnonneg n).1 (hnonneg n).2.1)).2 (hpoint n)
  have hnormProduct : vectorPositiveHaarNorm Q F =
      Real.sqrt (∑' n, c n ^ 2) := by
    unfold vectorPositiveHaarNorm
    rw [hproductEnergy]
  calc
    vectorPositiveHaarNorm Q F = Real.sqrt (∑' n, c n ^ 2) := hnormProduct
    _ ≤ Real.sqrt (∑' n, (a n + bseq n) ^ 2) := Real.sqrt_le_sqrt hsumle
    _ ≤ Real.sqrt (∑' n, a n ^ 2) + Real.sqrt (∑' n, bseq n ^ 2) :=
      sqrt_tsum_sq_add_le a bseq ha hb
    _ = M * positiveHaarNorm Q f.toFun + R * planarC1 * D * Real.sqrt E := by
      rw [hAroot, hBroot]

end ASDExplicitGamma.Triadic

end
