module

public import ASDExplicitGamma.Cold.SquareSineTest
public import Homogenization.Sobolev.Foundations.Hodge

/-! # Elimination of the square stream-function residual -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The mixed coefficient of one component of a vector field. -/
def squareVectorCoeff (Q : TriadicCube 2) (F : Vec 2 → Vec 2)
    (i : Fin 2) (p : Fin 2 → ℤ) : ℝ :=
  ∫ x, cubeSin Q i p x * F x i ∂normalizedCubeMeasure Q

/-- A zero-frequency sine mode vanishes identically. -/
theorem cubeSin_eq_zero_of_freq_eq_zero (Q : TriadicCube 2) (i : Fin 2) (p : Fin 2 → ℤ)
    (hf : cubeFreq Q p i = 0) : cubeSin Q i p = 0 := by
  have hp : p i = 0 := by
    simpa [cubeFreq, (cubeScaleFactor_pos' Q).ne', Real.pi_ne_zero] using hf
  funext x
  unfold cubeSin
  rw [boxMode_eq_prod_modeFactor]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [modeFactor, hp]

/-- On a square, vanishing divergence and curl coefficient equations kill every mixed
coefficient. The zero-frequency modes are treated explicitly. -/
theorem squareVectorCoeff_eq_zero_of_div_curl (Q : TriadicCube 2) (F : Vec 2 → Vec 2)
    (hdiv : ∀ p, cubeFreq Q p 0 * squareVectorCoeff Q F 0 p +
      cubeFreq Q p 1 * squareVectorCoeff Q F 1 p = 0)
    (hcurl : ∀ p, cubeFreq Q p 1 * squareVectorCoeff Q F 0 p -
      cubeFreq Q p 0 * squareVectorCoeff Q F 1 p = 0) :
    ∀ i p, squareVectorCoeff Q F i p = 0 := by
  intro i p
  by_cases hfreq : cubeFreq Q p 0 ^ 2 + cubeFreq Q p 1 ^ 2 = 0
  · have h0 : cubeFreq Q p 0 = 0 := by nlinarith [sq_nonneg (cubeFreq Q p 1)]
    have h1 : cubeFreq Q p 1 = 0 := by nlinarith [sq_nonneg (cubeFreq Q p 0)]
    fin_cases i
    · simp [squareVectorCoeff, cubeSin_eq_zero_of_freq_eq_zero Q 0 p h0]
    · simp [squareVectorCoeff, cubeSin_eq_zero_of_freq_eq_zero Q 1 p h1]
  · have hm0 : (cubeFreq Q p 0 ^ 2 + cubeFreq Q p 1 ^ 2) * squareVectorCoeff Q F 0 p = 0 := by
      linear_combination cubeFreq Q p 0 * hdiv p + cubeFreq Q p 1 * hcurl p
    have hm1 : (cubeFreq Q p 0 ^ 2 + cubeFreq Q p 1 ^ 2) * squareVectorCoeff Q F 1 p = 0 := by
      linear_combination cubeFreq Q p 1 * hdiv p - cubeFreq Q p 0 * hcurl p
    fin_cases i
    · exact (mul_eq_zero.mp hm0).resolve_left hfreq
    · exact (mul_eq_zero.mp hm1).resolve_left hfreq

/-- Mixed Parseval turns the coefficient equations into vanishing of an L² vector field. -/
theorem square_vector_ae_zero_of_div_curl (Q : TriadicCube 2) {F : Vec 2 → Vec 2}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hdiv : ∀ p, cubeFreq Q p 0 * squareVectorCoeff Q F 0 p +
      cubeFreq Q p 1 * squareVectorCoeff Q F 1 p = 0)
    (hcurl : ∀ p, cubeFreq Q p 1 * squareVectorCoeff Q F 0 p -
      cubeFreq Q p 0 * squareVectorCoeff Q F 1 p = 0) :
    F =ᵐ[normalizedCubeMeasure Q] 0 := by
  have hcoeff := squareVectorCoeff_eq_zero_of_div_curl Q F hdiv hcurl
  have hcoord (i : Fin 2) : (fun x => F x i) =ᵐ[normalizedCubeMeasure Q] 0 := by
    have hp := square_mixed_parseval Q {i} (hF i)
    have hz : ∫ x, F x i ^ 2 ∂normalizedCubeMeasure Q = 0 := by
      have hp' : HasSum (fun _ : Fin 2 → ℤ => (0 : ℝ))
          (∫ x, F x i ^ 2 ∂normalizedCubeMeasure Q) := by
        apply hp.congr_fun
        intro p
        change 0 = squareVectorCoeff Q F i p ^ 2
        rw [hcoeff, zero_pow (by decide)]
      exact hp'.unique hasSum_zero
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall (fun x => sq_nonneg (F x i))) (hF i).integrable_sq).mp hz
    filter_upwards [hae] with x hx
    exact sq_eq_zero_iff.mp hx
  filter_upwards [hcoord 0, hcoord 1] with x hx0 hx1
  ext i
  fin_cases i
  · exact hx0
  · exact hx1

end ASDExplicitGamma.Cold
