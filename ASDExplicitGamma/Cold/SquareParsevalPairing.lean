module

public import ASDExplicitGamma.Cold.SquareStreamFunction

/-! # Real mixed-basis Parseval for pairings -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- A real scalar mixed sine/cosine coefficient on the square. -/
def squareScalarCoeff (Q : TriadicCube 2) (O : Finset (Fin 2))
    (f : Vec 2 → ℝ) (p : Fin 2 → ℤ) : ℝ :=
  ∫ x, boxMode (cubeCorner Q) (cubeScaleFactor Q) O p x * f x ∂normalizedCubeMeasure Q

/-- Linearity of a mixed Fourier coefficient. -/
theorem squareScalarCoeff_add (Q : TriadicCube 2) (O : Finset (Fin 2))
    {f g : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) (p : Fin 2 → ℤ) :
    squareScalarCoeff Q O (fun x => f x + g x) p =
      squareScalarCoeff Q O f p + squareScalarCoeff Q O g p := by
  have hif := memLp_mode_mul (m := boxMode (cubeCorner Q) (cubeScaleFactor Q) O p)
    hf (continuous_boxMode _ _ _ _) (abs_boxMode_le _ _ _ _)
  have hig := memLp_mode_mul (m := boxMode (cubeCorner Q) (cubeScaleFactor Q) O p)
    hg (continuous_boxMode _ _ _ _) (abs_boxMode_le _ _ _ _)
  unfold squareScalarCoeff
  simp_rw [mul_add]
  exact integral_add hif hig

/-- Polarization of mixed Parseval gives the pairing identity, including its convergence. -/
theorem square_mixed_parseval_pairing (Q : TriadicCube 2) (O : Finset (Fin 2))
    {f g : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    HasSum (fun p => squareScalarCoeff Q O f p * squareScalarCoeff Q O g p)
      (∫ x, f x * g x ∂normalizedCubeMeasure Q) := by
  have hp := square_mixed_parseval Q O (f := fun x => f x + g x) (hf.add hg)
  have hpf := square_mixed_parseval Q O hf
  have hpg := square_mixed_parseval Q O hg
  have hs := ((hp.sub hpf).sub hpg).mul_left (1 / 2 : ℝ)
  have hfg : Integrable (fun x => f x * g x) (normalizedCubeMeasure Q) := hf.integrable_mul hg
  have heq : (fun x => (f x + g x) ^ 2) = (fun x => f x ^ 2 + g x ^ 2 + 2 * (f x * g x)) := by
    funext x; ring
  have hi : (∫ x, (f x + g x) ^ 2 ∂normalizedCubeMeasure Q) =
      (∫ x, f x ^ 2 ∂normalizedCubeMeasure Q) + (∫ x, g x ^ 2 ∂normalizedCubeMeasure Q) +
      2 * (∫ x, f x * g x ∂normalizedCubeMeasure Q) := by
    rw [heq, integral_add (f := fun x => f x ^ 2 + g x ^ 2)
      (g := fun x => 2 * (f x * g x)) (hf.integrable_sq.add hg.integrable_sq) (hfg.const_mul 2),
      integral_add hf.integrable_sq hg.integrable_sq, integral_const_mul]
  rw [hi] at hs
  have htarget : (1 / 2 : ℝ) *
      ((∫ x, f x ^ 2 ∂normalizedCubeMeasure Q) + (∫ x, g x ^ 2 ∂normalizedCubeMeasure Q) +
      2 * (∫ x, f x * g x ∂normalizedCubeMeasure Q) -
      (∫ x, f x ^ 2 ∂normalizedCubeMeasure Q) - (∫ x, g x ^ 2 ∂normalizedCubeMeasure Q)) =
      ∫ x, f x * g x ∂normalizedCubeMeasure Q := by ring
  rw [htarget] at hs
  apply hs.congr_fun
  intro p
  change squareScalarCoeff Q O f p * squareScalarCoeff Q O g p =
    (1 / 2 : ℝ) * (squareScalarCoeff Q O (fun x => f x + g x) p ^ 2 -
      squareScalarCoeff Q O f p ^ 2 - squareScalarCoeff Q O g p ^ 2)
  rw [squareScalarCoeff_add Q O hf hg]
  ring

end ASDExplicitGamma.Cold
