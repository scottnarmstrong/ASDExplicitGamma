module

public import ASDExplicitGamma.Gaussian.SquareLemmaV
public import ASDExplicitGamma.Gaussian.ShellBracket
public import ASDExplicitGamma.Gaussian.SquareDirections

/-! The actual physical bracket on arbitrary translated observation squares. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Inverse ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Model
noncomputable section

theorem square_shell_bracket
    (Q : TriadicCube 2) (j : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (hratio : diagMeshRadius Q j / L.1 ≤ 1 / 243)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let T := squareTrace Q ν σ k
    let B := pureFluxSourceTileHistory Q j (responseFramePlanarCoefficientField ν σ k)
    let H := squareQ3Directions Q b L
    Summable (fun n => (fderiv ℝ (squareTrace Q ν σ) k (H n)) ^ 2) ∧
    (∑' n, (fderiv ℝ (squareTrace Q ν σ) k (H n)) ^ 2) ≤
      16 * (b ^ 2 / σ ^ 2) * B ^ 2 * T * (T + 4) := by
  let β := b / σ
  let η : ℕ → PlanarW2Infinity Q := fun n =>
    mainQ3DirectionW2 Q β L (gaussEnumerated whiteBasis n)
  let H := squareQ3Directions Q b L
  let sB : Finset Unit := {()}
  let vB : Unit → ℝ := fun _ => β ^ 2
  let LB : Unit → ℝ := fun _ => L.1
  let B := pureFluxSourceTileHistory Q j (responseFramePlanarCoefficientField ν σ k)
  let T := squareTrace Q ν σ k
  have hrep : RepresentsQ3Band η sB vB LB :=
    main_shell_enumerated_representation Q β L
  have hvB : ∀ z ∈ sB, 0 ≤ vB z := fun _ _ => sq_nonneg β
  have hLB : ∀ z ∈ sB, 0 < LB z := fun _ _ => L.2
  have hlink : ∀ n, (η n).value.toFun =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => responseCoefficientExtension (H n) x / σ := by
    intro n
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet Q)] with x hx
    change q3Convolution (b / σ) L h3Zero (gaussEnumerated whiteBasis n) x = _
    rw [q3_convolution_div_frame,
      squareQ3Directions_value Q b L n hx]
  let κ := lemmaVH2BandConstant (diagMeshRadius Q j) (q3BandMoment sB vB LB 0)
    (q3BandMoment sB vB LB 2) (q3BandMoment sB vB LB 4)
  have hκ : κ ≤ 2 * Real.sqrt (β ^ 2) := by
    have hm0 : q3BandMoment sB vB LB 0 = β ^ 2 := by
      simp [q3BandMoment, sB, vB, LB]
    have hm2 : q3BandMoment sB vB LB 2 = β ^ 2 / L.1 ^ 2 := by
      simp [q3BandMoment, sB, vB, LB]
    have hm4 : q3BandMoment sB vB LB 4 = β ^ 2 / L.1 ^ 4 := by
      simp [q3BandMoment, sB, vB, LB]
    dsimp only [κ]
    rw [hm0, hm2, hm4]
    exact single_shell_h2_constant_le_two_sqrt (diagMeshRadius Q j) (β ^ 2) L.1
      (diagMeshRadius_pos Q j).le (sq_nonneg β) L.2 hratio
  have hκ0 : 0 ≤ κ := by
    dsimp [κ, lemmaVH2BandConstant, lemmaVH2C1, lemmaVH2C2]
    have hr := (diagMeshRadius_pos Q j).le
    have hv0 := q3BandMoment_nonneg sB vB LB 0 hvB hLB
    have hv2 := q3BandMoment_nonneg sB vB LB 2 hvB hLB
    have hv4 := q3BandMoment_nonneg sB vB LB 4 hvB hLB
    positivity
  have hV := square_lemmaV_of_interpolant Q j ν σ hν hσ k
    (diagInterpolant Q j) H (fun l => (η l).value)
    (fun l => (η l).value_memLp_top)
    (fun l i => (η l).gradient_memLp_top_volume i) hlink
    (diagInterpolant_affine_residual_memH10 Q j) κ hκ0
    (fun p u t c _ => lemmaV_H2_band Q j η sB vB LB hrep hvB hLB p u t c)
  have hκsq : 4 * κ ^ 2 ≤ 16 * β ^ 2 := by
    have hh := pow_le_pow_left₀ hκ0 hκ 2
    rw [mul_pow, Real.sq_sqrt (sq_nonneg β)] at hh
    linarith only [hh]
  have hT : 0 ≤ T :=
    traceDefect_nonneg_of_ellipticFieldOn_triCube (div_pos hν hσ)
      (lemmaV_frameCoefficient_isEllipticOn (measurableSet_cubeSet Q) ν σ hν hσ k)
      (by norm_num)
  have hhist := tile_history_le_source_history Q j ν σ hν hσ k
  have hhist0 := lemmaVTileHistory_nonneg Q j (responseFramePlanarCoefficientField ν σ k)
  have hhistSq : (lemmaVTileHistory Q j (responseFramePlanarCoefficientField ν σ k)) ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ hhist0 hhist 2
  refine ⟨hV.2.1, ?_⟩
  calc
    _ ≤ 4 * κ ^ 2 * (lemmaVTileHistory Q j
        (responseFramePlanarCoefficientField ν σ k)) ^ 2 * T * (T + 4) := hV.2.2
    _ ≤ 16 * β ^ 2 * B ^ 2 * T * (T + 4) := by
      have hp := mul_le_mul hκsq hhistSq (sq_nonneg _)
        (show 0 ≤ 16 * β ^ 2 by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hp hT) (by linarith only [hT])
    _ = 16 * (b ^ 2 / σ ^ 2) * B ^ 2 * T * (T + 4) := by
      dsimp [β]
      rw [div_pow]

end
end ASDExplicitGamma.Gaussian
