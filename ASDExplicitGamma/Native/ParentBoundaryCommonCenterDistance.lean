module

public import ASDExplicitGamma.Variational.LemmaVH2Remainder
public import ASDExplicitGamma.Triadic.PlanarDirectionOperations
public import ASDExplicitGamma.Variational.LemmaVDiag

/-! Translation-compatible common-center bounds. The center may lie outside
the observed child: its actual distance to that child is retained explicitly. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Response
open scoped BigOperators
noncomputable section

local instance parentCommonDistanceFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The common-center covariance value estimate requires only the actual
distance bound, and therefore survives translation of an observed child. -/
theorem parent_boundary_common_covariance_value_cap
    (v L S : ℝ) (hv : 0 ≤ v) (z x : Vec 2)
    (hdist : (x 0-z 0)^2 + (x 1-z 1)^2 ≤ S^2/2) :
    q3RemainderJetCovariance v L z .value .value x x ≤
      v*(lemmaVH2R1/2)*(S/L)^2 := by
  rw [q3RemainderJetCovariance_value_diagonal]
  have hp := mul_le_mul_of_nonneg_left
    (q3ProductCovariance_increment_bound (fun i => (x i-z i)/L)) hv
  have hg := div_le_div_of_nonneg_right hdist (sq_nonneg L)
  have hh := mul_le_mul_of_nonneg_left hg (mul_nonneg hv (by norm_num : (0:ℝ)≤78/5))
  have he : v*((78/5:ℝ)*(((x 0-z 0)/L)^2+((x 1-z 1)/L)^2)) ≤
      v*(lemmaVH2R1/2)*(S/L)^2 := by
    convert hh using 1 <;> simp only [lemmaVH2R1,div_pow,add_div] <;> ring
  calc
    _ = v*(2*(1-q3ProductCovariance (fun i => (x i-z i)/L))) := by ring
    _ ≤ _ := hp
    _ ≤ _ := he

/-- The finite common-center direction combination has its honest parent
radius bound even when the center lies outside the child observation cube. -/
theorem parent_boundary_common_direction_value_distance
    (Q : TriadicCube 2) (η : ℕ → PlanarW2Infinity Q) (v L S : ℝ) (z : Vec 2)
    (hrep : RepresentsQ3Remainder η v L z) (hv : 0 ≤ v)
    (t : Finset ℕ) (c : ℕ → ℝ) {x : Vec 2}
    (hdist : (x 0-z 0)^2 + (x 1-z 1)^2 ≤ S^2/2) :
    |(PlanarW2Infinity.linearCombination η t c).value.toFun x| ≤
      Real.sqrt (v*(lemmaVH2R1/2)*(S/L)^2)*Real.sqrt (∑ l ∈ t,c l^2) := by
  have hg := hrep .value .value x x
  have hs : Summable (fun l => (η l).value.toFun x^2) := by
    simpa only [q3DirectionJet,pow_two] using hg.1
  have hb := finite_coefficient_sq_le_tsum t c (fun l => (η l).value.toFun x) hs
  have he : (∑' l,(η l).value.toFun x^2)=q3RemainderJetCovariance v L z .value .value x x := by
    simpa only [q3DirectionJet,pow_two] using hg.2
  rw [he] at hb
  have hh := hb.trans (mul_le_mul_of_nonneg_left
    (parent_boundary_common_covariance_value_cap v L S hv z x hdist)
    (Finset.sum_nonneg fun l _ => sq_nonneg (c l)))
  have hr := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_sq_eq_abs,Real.sqrt_mul (Finset.sum_nonneg fun l _ => sq_nonneg (c l))] at hr
  simpa only [PlanarW2Infinity.linearCombination,h1_finset_sum_toFun,mul_comm] using hr

/-- Full H2, including the complete positive Haar series, at an arbitrary
common center with a proved geometric radius. -/
theorem parent_boundary_common_remainder_H2_distance
    (Q : TriadicCube 2) (j : ℕ) (η : ℕ → PlanarW2Infinity Q)
    (v L S : ℝ) (z : Vec 2) (hrep : RepresentsQ3Remainder η v L z)
    (hv : 0 ≤ v) (hL : 0 < L) (hS : 0 ≤ S)
    (hdist : ∀ x ∈ cubeSet Q,(x 0-z 0)^2+(x 1-z 1)^2 ≤ S^2/2)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) (t : Finset ℕ) (c : ℕ → ℝ) :
    let φ := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    (∀ R ∈ descendantsAtDepth Q j, ∀ b, Summable (fun n => (Real.sqrt 3)^(n+1)*energy R
      (cubeIncrement R (n+1) (fun x => lemmaVRowCombination I (fun l => (η l).value) φ t c x b)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVRowCombination I (fun l => (η l).value) φ t c)) ≤
      (Real.sqrt v * lemmaVH2Bn (S/L) (diagMeshRadius Q j/L)) *
        Real.sqrt (∑ l ∈ t,c l^2) * Real.sqrt (lemmaVTiledWeakEnergy Q j φ.grad) := by
  intro φ I
  let w := Real.sqrt (∑ l ∈ t,c l^2)
  have hw : 0 ≤ w := Real.sqrt_nonneg _
  have hval : ∀ᵐ x ∂normalizedCubeMeasure Q,
      |(PlanarW2Infinity.linearCombination η t c).value.toFun x| ≤
        Real.sqrt (v*(lemmaVH2R1/2)*(S/L)^2)*w := by
    filter_upwards [hilbert_ae_cubeSet Q] with x hx
    exact parent_boundary_common_direction_value_distance Q η v L S z hrep hv t c (hdist x hx)
  have hb := lemmaVH2_row_bound Q j (PlanarW2Infinity.linearCombination η t c) p u
    (mul_nonneg (Real.sqrt_nonneg _) hw) (mul_nonneg (Real.sqrt_nonneg _) hw)
    (mul_nonneg (Real.sqrt_nonneg _) hw) hval
    (Filter.Eventually.of_forall (q3Remainder_direction_gradient_cap η v L z hrep hv t c))
    (Filter.Eventually.of_forall (q3Remainder_direction_hessian_cap η v L z hrep hv hL t c))
  dsimp only at hb
  rw [← lemmaVRowCombination_linearCombination] at hb
  refine ⟨hb.1,hb.2.trans_eq ?_⟩
  rw [lemmaVH2RowConstant_scale,lemmaVH2RowConstant_remainder hv hL hS]

end
end ASDExplicitGamma.Native
