module

public import ASDExplicitGamma.Model.Q3DerivativeIncrement
public import ASDExplicitGamma.Variational.LemmaVH2BandDirections
public import Homogenization.Geometry.CubeMetric

/-! Exact common-center nonstationary covariance, without a stationarity surrogate. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Triadic
noncomputable section

 def q3RemainderJetCovariance (v L : ℝ) (z : Vec 2) : Q3SpatialJet → Q3SpatialJet → Vec 2 → Vec 2 → ℝ
  | .value, .value, x, y => q3ScaledJetCovariance v L .value .value x y -
      q3ScaledJetCovariance v L .value .value x z - q3ScaledJetCovariance v L .value .value z y + v
  | .value, .first i, x, y => q3ScaledJetCovariance v L .value (.first i) x y -
      q3ScaledJetCovariance v L .value (.first i) z y
  | .value, .second i j, x, y => q3ScaledJetCovariance v L .value (.second i j) x y -
      q3ScaledJetCovariance v L .value (.second i j) z y
  | .first i, .value, x, y => q3ScaledJetCovariance v L (.first i) .value x y -
      q3ScaledJetCovariance v L (.first i) .value x z
  | .second i j, .value, x, y => q3ScaledJetCovariance v L (.second i j) .value x y -
      q3ScaledJetCovariance v L (.second i j) .value x z
  | o, p, x, y => q3ScaledJetCovariance v L o p x y

/-- The directions represent ψ(x)-ψ(z), with the same center z for every direction. -/
def RepresentsQ3Remainder {Q : TriadicCube 2} (η : ℕ → PlanarW2Infinity Q) (v L : ℝ) (z : Vec 2) : Prop :=
  ∀ (o p : Q3SpatialJet) (x y : Vec 2),
    Summable (fun l => q3DirectionJet (η l) o x*q3DirectionJet (η l) p y) ∧
    (∑' l, q3DirectionJet (η l) o x*q3DirectionJet (η l) p y) = q3RemainderJetCovariance v L z o p x y

 theorem q3ScaledJetCovariance_values (v L : ℝ) (x y : Vec 2) :
    q3ScaledJetCovariance v L .value .value x y =
      v*q3ProductCovariance (fun i => (x i-y i)/L) := by
  simp only [q3ScaledJetCovariance, Q3SpatialJet.count, Q3SpatialJet.order, zero_add,
    pow_zero, mul_one, div_one, q3CovariancePartial_eq, iteratedDeriv_zero, q3ProductCovariance]

 theorem q3RemainderJetCovariance_value_diagonal (v L : ℝ) (z x : Vec 2) :
    q3RemainderJetCovariance v L z .value .value x x =
      2*v*(1-q3ProductCovariance (fun i => (x i-z i)/L)) := by
  rw [q3RemainderJetCovariance, q3ScaledJetCovariance_value_diagonal,
    q3ScaledJetCovariance_values, q3ScaledJetCovariance_values]
  have he : q3ProductCovariance (fun i => (z i-x i)/L) = q3ProductCovariance (fun i => (x i-z i)/L) := by
    unfold q3ProductCovariance
    simp only [show ∀ i, (z i-x i)/L = -((x i-z i)/L) from fun i => by ring, q3Cov_even]
  rw [he]
  ring

 theorem planar_cube_center_distance_sq (Q : TriadicCube 2) {x : Vec 2} (hx : x ∈ cubeSet Q) :
    (x 0-cubeCenter Q 0)^2+(x 1-cubeCenter Q 1)^2 ≤ (cubeScaleFactor Q)^2/2 := by
  have hi (i : Fin 2) : (x i-cubeCenter Q i)^2 ≤ (cubeScaleFactor Q/2)^2 := by
    have hb : |x i-cubeCenter Q i| ≤ cubeScaleFactor Q/2 := by
      apply abs_le.2
      have hh := hx i
      unfold cubeCenter
      constructor <;> nlinarith only [hh.1,hh.2.le]
    have hs := (sq_le_sq₀ (abs_nonneg _) (by unfold cubeScaleFactor; positivity)).2 hb
    simpa only [sq_abs] using hs
  nlinarith only [hi 0,hi 1]

 theorem q3RemainderJetCovariance_value_cap {v L : ℝ} (hv : 0 ≤ v)
    (Q : TriadicCube 2) {x : Vec 2} (hx : x ∈ cubeSet Q) :
    q3RemainderJetCovariance v L (cubeCenter Q) .value .value x x ≤
      v*(lemmaVH2R1/2)*(cubeScaleFactor Q/L)^2 := by
  rw [q3RemainderJetCovariance_value_diagonal]
  have hp := mul_le_mul_of_nonneg_left
    (q3ProductCovariance_increment_bound (fun i => (x i-cubeCenter Q i)/L)) hv
  have hg := div_le_div_of_nonneg_right (planar_cube_center_distance_sq Q hx) (sq_nonneg L)
  have hh := mul_le_mul_of_nonneg_left hg (mul_nonneg hv (by norm_num : (0:ℝ) ≤ 78/5))
  have he : v*((78/5:ℝ)*(((x 0-cubeCenter Q 0)/L)^2+((x 1-cubeCenter Q 1)/L)^2)) ≤
      v*(lemmaVH2R1/2)*(cubeScaleFactor Q/L)^2 := by
    convert hh using 1 <;> simp only [lemmaVH2R1, div_pow, add_div] <;> ring
  calc
    _ = v*(2*(1-q3ProductCovariance (fun i => (x i-cubeCenter Q i)/L))) := by ring
    _ ≤ _ := hp
    _ ≤ _ := he

end
end ASDExplicitGamma.Variational
