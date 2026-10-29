/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.SquareWeightedBounds
public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledProjected
public import ASDExplicitGamma.Inverse.PureFluxFeedbackCoefficient
public import ASDExplicitGamma.Gaussian.CovarianceRow
public import ASDExplicitGamma.Main.HilbertFiniteCoordinates
public import ASDExplicitGamma.Triadic.PositiveNormAggregation
public import ASDExplicitGamma.Gaussian.FiniteGenerator
public import ASDExplicitGamma.Gaussian.Q3Directions
public import ASDExplicitGamma.Inverse.PureFluxGeneratorMinimizerEnergy
public import ASDExplicitGamma.Inverse.PureFluxGeneratorHistory
public import ASDExplicitGamma.Gaussian.ShellBracket

/-! # CIR weighted generator adapter -/

@[expose] public section

open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Inverse ASDExplicitGamma.Model ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open MeasureTheory

namespace ASDExplicitGamma.AllOrder

/-- A response family in the exact finite-weighted form of the source theorem. `trace` is
the trace defect on each deterministic square, `inverseHistory` is its complete
inverse-history maximum, `halfGenerator` is the half covariance trace, and
`derivative` records the common Gaussian-coordinate derivatives. -/
structure CIRResponseFamily (ι Ω : Type*) where
  cells : Finset ι
  weight : ι → ℝ
  trace : ι → ℝ → Ω → ℝ
  inverseHistory : ι → ℝ → Ω → ℝ
  halfGenerator : ι → ℝ → Ω → ℝ
  derivative : ι → ℝ → Ω → ℕ → ℝ
  weight_nonneg : ∀ a ∈ cells, 0 ≤ weight a
  weight_sum_one : ∑ a ∈ cells, weight a = 1
  trace_nonneg : ∀ a ∈ cells, ∀ t ω, 0 ≤ trace a t ω
  history_nonneg : ∀ a ∈ cells, ∀ t ω, 0 ≤ inverseHistory a t ω

/-- The averaged trace defect `Y`. -/
def cirFamilyTrace {ι Ω : Type*} (F : CIRResponseFamily ι Ω)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑ a ∈ F.cells, F.weight a * F.trace a t ω

theorem cirFamilyTrace_nonneg {ι Ω : Type*} (F : CIRResponseFamily ι Ω)
    (t : ℝ) (ω : Ω) : 0 ≤ cirFamilyTrace F t ω := by
  unfold cirFamilyTrace
  exact Finset.sum_nonneg fun a ha =>
    mul_nonneg (F.weight_nonneg a ha) (F.trace_nonneg a ha t ω)

/-- The source observable `ℒ=Σ w B²(T+4)`. -/
def cirFamilyHistoryLoad {ι Ω : Type*} (F : CIRResponseFamily ι Ω)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑ a ∈ F.cells,
    F.weight a * F.inverseHistory a t ω ^ 2 * (F.trace a t ω + 4)

theorem cirFamilyHistoryLoad_nonneg {ι Ω : Type*} (F : CIRResponseFamily ι Ω)
    (t : ℝ) (ω : Ω) : 0 ≤ cirFamilyHistoryLoad F t ω := by
  unfold cirFamilyHistoryLoad
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg
    (mul_nonneg (F.weight_nonneg a ha) (sq_nonneg (F.inverseHistory a t ω)))
    (add_nonneg (F.trace_nonneg a ha t ω) (by norm_num))

/-- The averaged half-generator in the physical Gaussian directions. -/
def cirFamilyGenerator {ι Ω : Type*} (F : CIRResponseFamily ι Ω)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑ a ∈ F.cells, F.weight a * F.halfGenerator a t ω

/-- The derivative of the weighted response in the shared Gaussian coordinate. -/
def cirFamilyDerivative {ι Ω : Type*} (F : CIRResponseFamily ι Ω)
    (t : ℝ) (ω : Ω) (n : ℕ) : ℝ :=
  ∑ a ∈ F.cells, F.weight a * F.derivative a t ω n

/-- The common-coordinate carré du champ of the finite weighted family. -/
noncomputable def cirFamilyBracket {ι Ω : Type*} (F : CIRResponseFamily ι Ω)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑' n, cirFamilyDerivative F t ω n ^ 2

/-- Exact output for a finite weighted response family.
This interface permits arbitrary deterministic squares, including translated
children; the origin-cube checkpoint above is only one specialization. -/
structure CIRG4Output {ι Ω : Type*} (F : CIRResponseFamily ι Ω)
    (vbar : ℝ) : Prop where
  generator_bound : ∀ t ω,
    cirFamilyGenerator F t ω ≤ 19 * vbar * cirFamilyHistoryLoad F t ω
  derivative_summable : ∀ t ω,
    Summable (fun n => cirFamilyDerivative F t ω n ^ 2)
  bracket_bound : ∀ t ω,
    cirFamilyBracket F t ω ≤
      16 * vbar * cirFamilyTrace F t ω * cirFamilyHistoryLoad F t ω

/-- The response family attached to an actual finite family of translated
triadic squares and their physical q3 shell directions. -/
noncomputable def cirSquareResponseFamily {ι Ω : Type*}
    (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2) (j : ι → ℕ)
    (M : ABKModel 2) (frameLabel : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (k : (a : ι) → ℝ → Ω → ResponseCoefficient (openCubeSet (Q a)))
    (hw : ∀ a ∈ s, 0 ≤ w a)
    (hsum : ∑ a ∈ s, w a = 1) : CIRResponseFamily ι Ω := by
  let σ : ℝ := Annealed.sigmaBar M frameLabel
  refine {
    cells := s
    weight := w
    trace := fun a t ω => squareTrace (Q a) M.nu σ (k a t ω)
    inverseHistory := fun a t ω => pureFluxSourceTileHistory (Q a) (j a)
      (responseFramePlanarCoefficientField M.nu σ (k a t ω))
    halfGenerator := fun a t ω => (1 / 2 : ℝ) * modelCovarianceTrace
      (squareTrace (Q a) M.nu σ)
      (squareQ3Directions (Q a) b L) (k a t ω)
    derivative := fun a t ω n => fderiv ℝ (squareTrace (Q a) M.nu σ)
      (k a t ω) (squareQ3Directions (Q a) b L n)
    weight_nonneg := hw
    weight_sum_one := hsum
    trace_nonneg := ?_
    history_nonneg := ?_ }
  · intro a ha t ω
    exact traceDefect_nonneg_of_ellipticFieldOn_triCube
      (div_pos M.nu_pos (Annealed.sigmaBar_characterization M frameLabel).1)
      (lemmaV_frameCoefficient_isEllipticOn (measurableSet_cubeSet (Q a))
        M.nu (Annealed.sigmaBar M frameLabel) M.nu_pos
        (Annealed.sigmaBar_characterization M frameLabel).1 (k a t ω)) (by norm_num)
  · intro a ha t ω
    exact pureFlux_source_tile_history_nonneg (Q a) (j a)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M frameLabel)
        (k a t ω))

/-- Instantiate the arbitrary-square theorem at the completed
true frame for a finite weighted family. The common-coordinate bracket keeps
all cross terms between translated children. -/
theorem aoCir_square_output {ι Ω : Type*}
    (s : Finset ι) (w : ι → ℝ) (Q : ι → TriadicCube 2) (j : ι → ℕ)
    (M : ABKModel 2) (frameLabel : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hw : ∀ a ∈ s, 0 ≤ w a) (hsum : ∑ a ∈ s, w a = 1)
    (hratio : ∀ a ∈ s, diagMeshRadius (Q a) (j a) / L.1 ≤ 1 / 243)
    (k : (a : ι) → ℝ → Ω → ResponseCoefficient (openCubeSet (Q a))) :
    CIRG4Output (cirSquareResponseFamily s w Q j M frameLabel b L k hw hsum)
      (b ^ 2 / (Annealed.sigmaBar M frameLabel : ℝ) ^ 2) := by
  let σ : ℝ := Annealed.sigmaBar M frameLabel
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M frameLabel).1
  refine {
    generator_bound := ?_
    derivative_summable := ?_
    bracket_bound := ?_ }
  · intro t ω
    have h := (square_shell_weighted_generator_bracket s w Q j M.nu σ b M.nu_pos hσ L
      hw hratio (fun a => k a t ω)).1
    calc
      cirFamilyGenerator (cirSquareResponseFamily s w Q j M frameLabel b L k hw hsum) t ω =
          (1 / 2 : ℝ) * ∑ a ∈ s, w a * modelCovarianceTrace
            (squareTrace (Q a) M.nu σ) (squareQ3Directions (Q a) b L) (k a t ω) := by
        simp only [cirFamilyGenerator, cirSquareResponseFamily]
        change (∑ a ∈ s, w a * ((1 / 2 : ℝ) * modelCovarianceTrace
            (squareTrace (Q a) M.nu σ) (squareQ3Directions (Q a) b L)
            (k a t ω))) = _
        calc
          _ = ∑ a ∈ s, (1 / 2 : ℝ) * (w a * modelCovarianceTrace
              (squareTrace (Q a) M.nu σ) (squareQ3Directions (Q a) b L)
              (k a t ω)) := by
            apply Finset.sum_congr rfl
            intro a ha
            ring
          _ = _ := by rw [Finset.mul_sum]
      _ ≤ 19 * (b ^ 2 / σ ^ 2) *
          cirFamilyHistoryLoad
            (cirSquareResponseFamily s w Q j M frameLabel b L k hw hsum) t ω := by
        simpa [cirFamilyHistoryLoad, cirSquareResponseFamily, σ] using h
  · intro t ω
    change Summable (fun n =>
      (∑ a ∈ s, w a * fderiv ℝ (squareTrace (Q a) M.nu σ) (k a t ω)
        (squareQ3Directions (Q a) b L n)) ^ 2)
    exact (square_shell_weighted_generator_bracket s w Q j M.nu σ b M.nu_pos hσ L
      hw hratio (fun a => k a t ω)).2.1
  · intro t ω
    change (∑' n, (∑ a ∈ s,
      w a * fderiv ℝ (squareTrace (Q a) M.nu σ) (k a t ω)
        (squareQ3Directions (Q a) b L n)) ^ 2) ≤
      16 * (b ^ 2 / σ ^ 2) *
        (∑ a ∈ s, w a * squareTrace (Q a) M.nu σ (k a t ω)) *
        (∑ a ∈ s, w a *
          pureFluxSourceTileHistory (Q a) (j a)
            (responseFramePlanarCoefficientField M.nu σ (k a t ω)) ^ 2 *
          (squareTrace (Q a) M.nu σ (k a t ω) + 4))
    exact (square_shell_weighted_generator_bracket s w Q j M.nu σ b M.nu_pos hσ L
      hw hratio (fun a => k a t ω)).2.2

end ASDExplicitGamma.AllOrder
