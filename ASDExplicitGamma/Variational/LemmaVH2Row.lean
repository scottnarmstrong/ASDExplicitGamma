module

public import ASDExplicitGamma.Triadic.PlanarRowProduct
public import ASDExplicitGamma.Triadic.PositiveNormAggregation
public import ASDExplicitGamma.Triadic.DiagEstimates
public import ASDExplicitGamma.Variational.LemmaVH2Constants
public import ASDExplicitGamma.Variational.LemmaVRowEstimate

/-! The concrete DIAG row estimate before inserting the three source covariance families. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open scoped BigOperators
noncomputable section

local instance lemmaVH2RowFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

 theorem lemmaVH2_rowField_eq {U : Set (Vec 2)} (I : H1Function U →ₗ[ℝ] H1Function U) (η v : H1Function U) :
    lemmaVPlanarRowField I η v = fun x => planarQuarterTurn
      (fun i => η.toFun x*(I v).grad x i-η.grad x i*(v-I v).toFun x) := by
  funext x i
  fin_cases i <;>
    simp [lemmaVPlanarRowField, lemmaVPlanarWeakColumnDivergence, responsePlanarJ, matVecMul,
      Fin.sum_univ_two, planarQuarterTurn, Pi.smul_apply, smul_eq_mul] <;> ring

/-- Exact per-tile row estimate for the source affine-data DIAG map. -/
theorem lemmaVH2_tile_row_bound (Q : TriadicCube 2) (j : ℕ) (η : PlanarW2Infinity Q)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j)
    {A G H : ℝ} (hA : 0 ≤ A) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hval : ∀ᵐ x ∂normalizedCubeMeasure Q, |η.value.toFun x| ≤ A)
    (hgrad : ∀ᵐ x ∂normalizedCubeMeasure Q, planarEuclideanNorm (planarW1Value η.gradient x) ≤ G)
    (hhess : ∀ᵐ x ∂normalizedCubeMeasure Q, planarFrobeniusNorm (planarW1Derivative η.gradient x) ≤ H) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    (∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy R
      (cubeIncrement R (k+1) (fun x => lemmaVPlanarRowField I η.value v x i)))) ∧
    vectorPositiveHaarNorm R (lemmaVPlanarRowField I η.value v) ≤
      (A+diagMeshRadius Q j*planarC1*G)*vectorPositiveHaarNorm R (I v).grad+
      G*positiveHaarNorm R (v-I v).toFun+diagMeshRadius Q j*planarC1*H*Real.sqrt (energy R (v-I v).toFun) := by
  intro v I
  let ηR := η.restrict hR
  let rR := (v-I v).restrictToOpenSubcube hR
  have heq : lemmaVPlanarRowField I η.value v = planarRowProduct ηR (I v).grad rR := by
    rw [lemmaVH2_rowField_eq]
    rfl
  have h := planarRowProduct_bound R ηR (I v).grad rR
    (fun i => memLp_on_descendant_of_memLp hR ((I v).grad_memL2_normalizedCubeMeasure i))
    (fun i => diagInterpolant_gradient_summable Q j p u R hR i) hA hG hH
    (hilbert_ae_descendant hR hval) (hilbert_ae_descendant hR hgrad) (hilbert_ae_descendant hR hhess)
  rw [← heq] at h
  simpa only [rR, diagMeshRadius, cubeScaleFactor_descendant_eq_div_pow hR, H1Function.restrictToOpenSubcube_toFun] using h

/-- Broken row estimate with exact pre-rounding constants, before the three source routes. -/
theorem lemmaVH2_row_bound_exact (Q : TriadicCube 2) (j : ℕ) (η : PlanarW2Infinity Q)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) {A G H : ℝ} (hA : 0 ≤ A) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hval : ∀ᵐ x ∂normalizedCubeMeasure Q, |η.value.toFun x| ≤ A)
    (hgrad : ∀ᵐ x ∂normalizedCubeMeasure Q, planarEuclideanNorm (planarW1Value η.gradient x) ≤ G)
    (hhess : ∀ᵐ x ∂normalizedCubeMeasure Q, planarFrobeniusNorm (planarW1Derivative η.gradient x) ≤ H) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    (∀ R ∈ descendantsAtDepth Q j, ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy R
      (cubeIncrement R (k+1) (fun x => lemmaVPlanarRowField I η.value v x i)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVPlanarRowField I η.value v)) ≤
      (A+diagMeshRadius Q j*(planarC1+2/Real.pi+1/2)*G+
        (diagMeshRadius Q j)^2*planarC1*(planarC0+1/2)*H)*Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad) := by
  intro v I
  let r := diagMeshRadius Q j
  have hr : 0 ≤ r := (diagMeshRadius_pos Q j).le
  have hc1 : 0 ≤ planarC1 := Real.sqrt_nonneg _
  have hlocal (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :=
    lemmaVH2_tile_row_bound Q j η p u R hR hA hG hH hval hgrad hhess
  refine ⟨fun R hR => (hlocal R hR).1, ?_⟩
  have hagg := sqrt_descendantsAverage_energy_bound_three Q j
    (fun R => vectorPositiveHaarEnergy R (lemmaVPlanarRowField I η.value v))
    (fun R => vectorPositiveHaarEnergy R (I v).grad)
    (fun R => primalEnergy R (Real.sqrt 3) (v-I v).toFun)
    (fun R => energy R (v-I v).toFun)
    (add_nonneg hA (mul_nonneg (mul_nonneg hr hc1) hG)) hG (mul_nonneg (mul_nonneg hr hc1) hH)
    (fun R _ => vectorPositiveHaarEnergy_nonneg R _) (fun R _ => vectorPositiveHaarEnergy_nonneg R _)
    (fun R _ => primalEnergy_nonneg R _ (Real.sqrt_nonneg _) _) (fun R _ => energy_nonneg R _)
    (fun R hR => (hlocal R hR).2)
  rw [← energy_eq_descendantsAverage Q j (v-I v).memL2_normalizedCubeMeasure] at hagg
  have h1 := mul_le_mul_of_nonneg_left (diagInterpolant_gradient_estimate Q j p u)
    (add_nonneg hA (mul_nonneg (mul_nonneg hr hc1) hG))
  have h2 := mul_le_mul_of_nonneg_left (diagInterpolant_residual_positive_estimate Q j p u) hG
  have h3 := mul_le_mul_of_nonneg_left (diagInterpolant_residual_L2_estimate Q j p u) (mul_nonneg (mul_nonneg hr hc1) hH)
  have ht := hagg.trans (add_le_add (add_le_add h1 h2) h3)
  convert ht using 1
  · rfl
  · dsimp only [v, r]
    ring



/-- The source 340 outward row coefficient, with actual convergence on every tile. -/
theorem lemmaVH2_row_bound (Q : TriadicCube 2) (j : ℕ) (η : PlanarW2Infinity Q)
    (p : Vec 2) (u : H10Function (openCubeSet Q)) {A G H : ℝ} (hA : 0 ≤ A) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hval : ∀ᵐ x ∂normalizedCubeMeasure Q, |η.value.toFun x| ≤ A)
    (hgrad : ∀ᵐ x ∂normalizedCubeMeasure Q, planarEuclideanNorm (planarW1Value η.gradient x) ≤ G)
    (hhess : ∀ᵐ x ∂normalizedCubeMeasure Q, planarFrobeniusNorm (planarW1Derivative η.gradient x) ≤ H) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    let I := diagInterpolant Q j
    (∀ R ∈ descendantsAtDepth Q j, ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy R
      (cubeIncrement R (k+1) (fun x => lemmaVPlanarRowField I η.value v x i)))) ∧
    Real.sqrt (lemmaVTiledPositiveEnergy Q j (lemmaVPlanarRowField I η.value v)) ≤
      lemmaVH2RowConstant (diagMeshRadius Q j) A G H*Real.sqrt (lemmaVTiledWeakEnergy Q j v.grad) := by
  intro v I
  have hs := lemmaVH2_row_bound_exact Q j η p u hA hG hH hval hgrad hhess
  refine ⟨hs.1, hs.2.trans ?_⟩
  have hr : 0 ≤ diagMeshRadius Q j := (diagMeshRadius_pos Q j).le
  have hc1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left lemmaVH2C1_outward hr) hG
  have hc2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left lemmaVH2C2_outward (sq_nonneg (diagMeshRadius Q j))) hH
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  unfold lemmaVH2RowConstant
  nlinarith only [hc1,hc2]

end
end ASDExplicitGamma.Variational
