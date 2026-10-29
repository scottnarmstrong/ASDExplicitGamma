module

public import ASDExplicitGamma.Inverse.LaterBandW2
public import ASDExplicitGamma.Gaussian.SupMeanShellSupremum

/-! Actual finite-band derivative tensors and compact-square norm payment. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Triadic
noncomputable section

/-- The actual later tensor sum, retaining its full skew Frobenius factor. -/
def laterBandTensor {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet)
    (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) : EuclideanSpace ℝ ι :=
  ∑ k ∈ Finset.Ioc n J, weights k • supMeanShellTensor o x (ω.val k)

/-- Every point of the actual closed observation square pays the same
compact tensor norms. No probabilistic bound is a premise. -/
theorem later_band_tensor_norm_le {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet)
    (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (c : Vec 2) (s : ℝ)
    {x : Vec 2} (hx : x ∈ supMeanClosedSquare c s) :
    ‖laterBandTensor o n J weights ω x‖ ≤
      ∑ k ∈ Finset.Ioc n J, |weights k| *‖supMeanShellSquareTensor o c s (ω.val k)‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (supMeanShellSquareTensor o c s (ω.val k)).norm_coe_le_norm ⟨x,hx⟩

/-- The first tensor is sqrt(2) times the actual scalar gradient coordinates. -/
theorem later_band_first_tensor_eq (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    laterBandTensor Q3SpatialJet.first n J weights ω x =
      Real.sqrt 2 • (WithLp.toLp 2 (fun i => laterScalarFirst n J weights ω i x) : EuclideanSpace ℝ (Fin 2)) := by
  ext i
  simp only [laterBandTensor,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,supMeanShellTensor,
    supMeanShellJetScalar,supMeanJetObservation,shellDerivativeEval,laterScalarFirst]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The full second tensor is sqrt(2) times the actual scalar Hessian coordinates. -/
theorem later_band_second_tensor_eq (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    laterBandTensor (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) n J weights ω x =
      Real.sqrt 2 • (WithLp.toLp 2 (fun i : Fin 2 × Fin 2 => ∑ k ∈ Finset.Ioc n J,
        weights k*shellScalarFirstDerivative (basisVec i.1) (ω.val k) x (basisVec i.2)) : EuclideanSpace ℝ (Fin 2 × Fin 2)) := by
  ext i
  simp only [laterBandTensor,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,supMeanShellTensor,
    supMeanShellJetScalar,supMeanJetObservation,shellDerivativeEval]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact full Frobenius payment for the Sobolev witness's gradient. -/
theorem later_band_first_tensor_norm (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    ‖laterBandTensor Q3SpatialJet.first n J weights ω x‖ =
      Real.sqrt 2*planarEuclideanNorm (planarW1Value (laterBandW2 Q n J weights ω).gradient x) := by
  rw [later_band_first_tensor_eq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  congr 1
  rw [EuclideanSpace.norm_eq]
  unfold planarEuclideanNorm planarW1Value
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [later_band_w2_first]
  simp only [Real.norm_eq_abs,sq_abs]

/-- Exact full Frobenius payment for the Sobolev witness's Hessian. -/
theorem later_band_second_tensor_norm (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    ‖laterBandTensor (fun i : Fin 2 × Fin 2 => Q3SpatialJet.second i.1 i.2) n J weights ω x‖ =
      Real.sqrt 2*planarFrobeniusNorm (planarW1Derivative (laterBandW2 Q n J weights ω).gradient x) := by
  rw [later_band_second_tensor_eq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  congr 1
  rw [EuclideanSpace.norm_eq]
  unfold planarFrobeniusNorm planarW1Derivative
  rw [Fintype.sum_prod_type]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [later_band_w2_second]
  simp only [Real.norm_eq_abs,sq_abs]

end
end ASDExplicitGamma.Inverse
