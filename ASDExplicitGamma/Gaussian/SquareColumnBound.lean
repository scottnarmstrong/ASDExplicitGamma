module

public import ASDExplicitGamma.Gaussian.SquareColumn
public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledProjected
public import ASDExplicitGamma.Inverse.PureFluxFeedbackCoefficient
public import ASDExplicitGamma.Gaussian.CovarianceRow
public import ASDExplicitGamma.Main.HilbertFiniteCoordinates
public import ASDExplicitGamma.Triadic.PositiveNormAggregation

/-! Complete physical source-column bounds on arbitrary translated squares. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Numerics
open scoped BigOperators
noncomputable section

local instance squareColumnBoundFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem square_column_coefficient_le_generatorKA {r b L : ℝ}
    (hr : 0 ≤ r) (hL : 0 < L) :
    Real.sqrt (b ^ 2) + r * (36 / 25) * Real.sqrt ((156 / 5) * b ^ 2 / L ^ 2) +
      r ^ 2 * (57 / 200) * Real.sqrt ((46488 / 25) * b ^ 2 / L ^ 4) ≤
      generatorKA (r / L) * |b| := by
  have hc := q3_source_coefficient_le_generatorKA hr (abs_nonneg b) hL
  simp only [mainQ3RemainderConstant, sq_abs] at hc
  have hlin : r * (36 / 25 : ℝ) * Real.sqrt ((156 / 5) * b ^ 2 / L ^ 2) ≤
      (2018 / 1000) * r * Real.sqrt ((156 / 5) * b ^ 2 / L ^ 2) := by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by norm_num : (36 / 25 : ℝ) ≤ 2018 / 1000) hr)
      (Real.sqrt_nonneg ((156 / 5) * b ^ 2 / L ^ 2))
    convert h using 1 <;> ring
  rw [Real.sqrt_sq_eq_abs]
  linarith only [hc, hlin]

theorem squareQ3RowEnergy_frame (Q : TriadicCube 2) (b σ : ℝ)
    (L : {l : ℝ // 0 < l}) (m : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) (l : whiteBasisIndex) :
    squareQ3RowEnergy Q b σ L m p u l =
      (σ⁻¹) ^ 2 * squareQ3RowEnergy Q b 1 L m p u l := by
  let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
  let I := diagInterpolant Q m
  have hη : squareQ3BasisMultiplier Q b σ L l =
      (σ⁻¹ : ℝ) • squareQ3BasisMultiplier Q b 1 L l := by
    simp only [squareQ3BasisMultiplier, inv_one, one_smul]
  have hfield : lemmaVPlanarRowField I (squareQ3BasisMultiplier Q b σ L l) v =
      fun x => (σ⁻¹ : ℝ) •
        lemmaVPlanarRowField I (squareQ3BasisMultiplier Q b 1 L l) v x := by
    rw [hη, pureFluxPlanarRowField_smul]
  have hpoint (U : TriadicCube 2) :
      vectorPositiveHaarEnergy U
        (lemmaVPlanarRowField I (squareQ3BasisMultiplier Q b σ L l) v) =
      (σ⁻¹) ^ 2 * vectorPositiveHaarEnergy U
        (lemmaVPlanarRowField I (squareQ3BasisMultiplier Q b 1 L l) v) := by
    rw [hfield]
    unfold vectorPositiveHaarEnergy
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [sensitivity_primalEnergy_smul]
    rw [Finset.mul_sum]
  unfold squareQ3RowEnergy
  change descendantsAverage Q m (fun U => vectorPositiveHaarEnergy U
      (lemmaVPlanarRowField I (squareQ3BasisMultiplier Q b σ L l) v)) = _
  simp_rw [hpoint]
  rw [descendantsAverage_mul_left]

/-- The actual physical source column is Hilbert--Schmidt on every aligned
tiling of any translated observation square. -/
theorem square_q3_row_source_trace_bound
    (Q : TriadicCube 2) (b σ : ℝ) (L : {l : ℝ // 0 < l}) (m : ℕ)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Summable (squareQ3RowEnergy Q b σ L m p u) ∧
      Real.sqrt (∑' l, squareQ3RowEnergy Q b σ L m p u l) ≤
        |σ⁻¹| * |b| * generatorKA (diagMeshRadius Q m / L.1) *
          Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad) := by
  intro v
  let C := |σ⁻¹| * |b| * generatorKA (diagMeshRadius Q m / L.1) *
    Real.sqrt (lemmaVTiledWeakEnergy Q m v.grad)
  have hρ0 : 0 ≤ diagMeshRadius Q m / L.1 :=
    div_nonneg (diagMeshRadius_pos Q m).le L.2.le
  have hC : 0 ≤ C := by
    dsimp [C, generatorKA]
    positivity
  have hn (l : whiteBasisIndex) : 0 ≤ squareQ3RowEnergy Q b σ L m p u l := by
    unfold squareQ3RowEnergy descendantsAverage
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun U _ => vectorPositiveHaarEnergy_nonneg U _)
  have hfinite (s : Finset whiteBasisIndex) :
      Real.sqrt (∑ l ∈ s, squareQ3RowEnergy Q b σ L m p u l) ≤ C := by
    have heq : (∑ l ∈ s, squareQ3RowEnergy Q b σ L m p u l) =
        (σ⁻¹) ^ 2 * ∑ l ∈ s, squareQ3RowEnergy Q b 1 L m p u l := by
      calc
        _ = ∑ l ∈ s, (σ⁻¹) ^ 2 * squareQ3RowEnergy Q b 1 L m p u l :=
          Finset.sum_congr rfl (fun l _ => squareQ3RowEnergy_frame Q b σ L m p u l)
        _ = _ := (Finset.mul_sum _ _ _).symm
    rw [heq, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
    have hunit := square_row_trace_finset_sharp Q b L m p u s
    have hc := square_column_coefficient_le_generatorKA (b := b)
      (diagMeshRadius_pos Q m).le L.2
    have hu := hunit.trans (mul_le_mul_of_nonneg_right hc
      (Real.sqrt_nonneg (lemmaVTiledWeakEnergy Q m v.grad)))
    have hs := mul_le_mul_of_nonneg_left hu (abs_nonneg (σ⁻¹))
    convert hs using 1 <;> dsimp [C] <;> ring
  have hsq (s : Finset whiteBasisIndex) :
      (∑ l ∈ s, squareQ3RowEnergy Q b σ L m p u l) ≤ C ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hfinite s) 2
    rw [Real.sq_sqrt (Finset.sum_nonneg fun l _ => hn l)] at h
    exact h
  exact ⟨summable_of_sum_le hn hsq,
    (Real.sqrt_le_iff).2 ⟨hC, Real.tsum_le_of_sum_le hn hsq⟩⟩

end
end ASDExplicitGamma.Gaussian
