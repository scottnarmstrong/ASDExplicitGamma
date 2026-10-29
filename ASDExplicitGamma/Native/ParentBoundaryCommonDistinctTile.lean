module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorValueRow
public import ASDExplicitGamma.Native.ParentBoundaryCommonCenterHilbertTrace
public import ASDExplicitGamma.Main.HilbertCoordinateMembership
public import ASDExplicitGamma.Main.HilbertPositiveTriangle
public import ASDExplicitGamma.Triadic.DiagEstimates
public import ASDExplicitGamma.Triadic.PositiveNormAggregation

/-! The common-parent-center covariance feedback row. Distinct actual
source potentials are retained in all covariance directions. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open scoped BigOperators
noncomputable section

local instance parentCommonDistinctRowFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The centered row sum retains a distinct potential in each covariance direction. -/
def parentBoundaryCommonDistinctRow {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (P Q : TriadicCube 2) (m : ℕ)
    (z : ι → H10Function (openCubeSet Q)) : Vec 2 → Vec 2 :=
  fun x => ∑ l ∈ s, lemmaVPlanarRowField (diagInterpolant Q m)
    (parentBoundaryCommonQ3Direction P Q b L (e l)).value (z l).toH1Function x

theorem parent_boundary_common_distinct_tile_bound {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (P Q : TriadicCube 2) (m : ℕ)
    (hQP : cubeSet Q ⊆ cubeSet P)
    (z : ι → H10Function (openCubeSet Q))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q m) :
    let I := diagInterpolant Q m
    let S := parentBoundaryCommonDistinctRow e s b L P Q m z
    let M := Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2)
    let G := Real.sqrt ((78/5:ℝ)*b^2/L.1^2)
    let H := Real.sqrt ((23244/25:ℝ)*b^2/L.1^4)
    (∀ i : Fin 2, Summable (fun k => (Real.sqrt 3)^(k+1)*energy U
      (cubeIncrement U (k+1) (fun x => S x i)))) ∧
    vectorPositiveHaarNorm U S ≤
      (M+cubeScaleFactor U*planarC1*G)*
        Real.sqrt (∑ l : s, vectorPositiveHaarEnergy U (I (z l).toH1Function).grad) +
      G*Real.sqrt (∑ l : s, primalEnergy U (Real.sqrt 3)
        ((z l).toH1Function-I (z l).toH1Function).toFun) +
      cubeScaleFactor U*planarC1*H*Real.sqrt (∑ l : s, energy U
        ((z l).toH1Function-I (z l).toH1Function).toFun) := by
  intro I S M G H
  let F : Vec 2 → EuclideanSpace ℝ (s × Fin 2) :=
    fun x => WithLp.toLp 2 (fun p => (I (z p.1).toH1Function).grad x p.2)
  let R : Vec 2 → EuclideanSpace ℝ s := fun x => WithLp.toLp 2
    (fun l => (-((z l).toH1Function-I (z l).toH1Function)).toFun x)
  let A := pureFluxQ3CenteredValueRow e s b L P U
  let B := pureFluxQ3DerivativeRow e s b L U
  let C := fun x => A.toFun x (F x)+B.toFun x (R x)
  have hzero (l : ι) : lemmaVAffinePotential
      (isOpenBoundedConvexDomain_openCubeSet Q) 0 (z l) = (z l).toH1Function := by
    ext x
    · simp only [lemmaVAffinePotential, H1Function.add_toFun,
        H1Function.affineOnIsSobolevRegularDomain_apply]
      simp
    · simp only [lemmaVAffinePotential, H1Function.add_grad,
        H1Function.affineOnIsSobolevRegularDomain_grad]
      simp only [zero_add]
  have hFmem : MemLp F 2 (normalizedCubeMeasure U) := by
    apply memLp_piLp_iff.mpr
    intro p
    exact memLp_on_descendant_of_memLp hU
      ((I (z p.1).toH1Function).grad_memL2_normalizedCubeMeasure p.2)
  have hFP := main_hilbert_summable_of_coordinates U hFmem (fun p => by
    simpa only [hzero, F, WithLp.ofLp_toLp, I] using
      diagInterpolant_gradient_summable Q m 0 (z p.1) U hU p.2)
  have hRmem : MemLp R 2 (normalizedCubeMeasure U) := by
    apply memLp_piLp_iff.mpr
    intro l
    exact ((-((z l).toH1Function-I (z l).toH1Function)).restrictToOpenSubcube hU).memL2_normalizedCubeMeasure
  have hRP := main_hilbert_summable_of_coordinates U hRmem (fun l => by
    let r := (-((z l).toH1Function-I (z l).toH1Function)).restrictToOpenSubcube hU
    exact positiveHaarIncrementSeries_summable U r.memL2_normalizedCubeMeasure
      r.grad_memL2_normalizedCubeMeasure r.hasWeakGradient)
  have hq : 1 < Real.sqrt 3 := by
    nlinarith only [Real.sqrt_nonneg (3:ℝ), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hq9 : Real.sqrt 3 < 9 := by
    nlinarith only [Real.sqrt_nonneg (3:ℝ), Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  have hM : ∀ᵐ x ∂normalizedCubeMeasure U, ‖A.toFun x‖ ≤ M := by
    filter_upwards [hilbert_ae_cubeSet U] with x hx
    exact pureFluxQ3CenteredValueRow_norm_le e s b L P U
      (hQP (cubeSet_subset_of_mem_descendantsAtDepth hU hx))
  have hG : ∀ᵐ x ∂normalizedCubeMeasure U, ‖B.toFun x‖ ≤ G :=
    Filter.Eventually.of_forall (pureFluxQ3DerivativeRow_norm_le e s b L U)
  have hDA : ∀ᵐ x ∂normalizedCubeMeasure U, ∀ c : EuclideanSpace ℝ (s × Fin 2),
      (∑ i, ‖A.grad x i c‖^2) ≤ G^2*‖c‖^2 := by
    apply Filter.Eventually.of_forall
    intro x c
    dsimp only [G]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (78/5:ℝ)*b^2/L.1^2)]
    exact pureFluxQ3CenteredValueRow_combined_gradient_le e s b L P U x c
  have hDB : ∀ᵐ x ∂normalizedCubeMeasure U, ∀ c : EuclideanSpace ℝ s,
      (∑ i, ‖B.grad x i c‖^2) ≤ H^2*‖c‖^2 := by
    apply Filter.Eventually.of_forall
    intro x c
    dsimp only [H]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (23244/25:ℝ)*b^2/L.1^4)]
    exact pureFluxQ3DerivativeRow_combined_gradient_le e s b L U x c
  have ha := pureFlux_positive_product_of_combined_bounds A hq hq9 hFmem hFP
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hM hDA
  have hb := pureFlux_positive_product_of_combined_bounds B hq hq9 hRmem hRP
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hG hDB
  have hc1 : Real.sqrt (haarPoincareM2 (Real.sqrt 3)) = planarC1 := by
    unfold haarPoincareM2
    rw [mul_comm (1-Real.sqrt 3/9)]
    rfl
  rw [hc1] at ha hb
  have hAmem := A.product_memLp hFmem
  have hBmem := B.product_memLp hRmem
  have hCmem : MemLp C 2 (normalizedCubeMeasure U) := hAmem.add hBmem
  have hc := main_hilbert_positive_add U hAmem hBmem ha.1 hb.1
  have hCcoord (i : Fin 2) : MemLp (fun x => (C x).ofLp i) 2 (normalizedCubeMeasure U) := by
    let pr : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) i
    simpa only [pr, Function.comp_def, PiLp.proj_apply] using pr.comp_memLp' hCmem
  have hCP (i : Fin 2) := main_hilbert_coordinate_summable U hCmem hc.1 i
  have hrow : S = fun x => planarQuarterTurn (fun i => (C x).ofLp i) := by
    funext x i
    change (∑ l ∈ s, lemmaVPlanarRowField I
      (parentBoundaryCommonQ3Direction P Q b L (e l)).value (z l).toH1Function x) i = _
    simp only [Finset.sum_apply, lemmaVH2_rowField_eq]
    rw [← Finset.sum_coe_sort s]
    fin_cases i <;>
      simp [C, A, B, F, R, pureFluxQ3CenteredValueRow_apply,
        pureFluxQ3DerivativeRow_apply, parent_boundary_common_q3_direction_value,
        parent_boundary_common_q3_direction_grad, planarQuarterTurn, H1Function.neg_toFun,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        mul_add, add_mul, sub_mul, mul_sub, mul_comm, mul_left_comm, mul_assoc] <;> ring
  have hnorm : vectorPositiveHaarNorm U S = hilbertPositiveHaarNorm U (Real.sqrt 3) C := by
    rw [hrow, vectorPositiveHaarNorm_quarterTurn]
    simpa only [WithLp.toLp_ofLp] using
      (main_hilbertPositive_eq_vectorPositive U hCcoord hCP).symm
  have hPF : hilbertPositiveHaarNorm U (Real.sqrt 3) F =
      Real.sqrt (∑ l : s, vectorPositiveHaarEnergy U (I (z l).toH1Function).grad) := by
    unfold hilbertPositiveHaarNorm
    rw [main_hilbertPrimalEnergy_euclidean U hFmem hFP]
    simp only [F, WithLp.ofLp_toLp, Fintype.sum_prod_type, vectorPositiveHaarEnergy]
  have hPR : hilbertPositiveHaarNorm U (Real.sqrt 3) R =
      Real.sqrt (∑ l : s, primalEnergy U (Real.sqrt 3)
        ((z l).toH1Function-I (z l).toH1Function).toFun) := by
    unfold hilbertPositiveHaarNorm
    rw [main_hilbertPrimalEnergy_euclidean U hRmem hRP]
    simp only [R, WithLp.ofLp_toLp, H1Function.neg_toFun, primalEnergy_neg]
  have hLR : hilbertL2Norm U R = Real.sqrt (∑ l : s, energy U
      ((z l).toH1Function-I (z l).toH1Function).toFun) := by
    unfold hilbertL2Norm
    rw [main_hilbertEnergy_euclidean U hRmem]
    simp only [R, WithLp.ofLp_toLp, H1Function.neg_toFun, energy_neg]
  have hLF := main_hilbertL2_le_positive U hFmem hFP
  have hcoef : 0 ≤ cubeScaleFactor U*planarC1*G :=
    mul_nonneg (mul_nonneg (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' U).le
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine ⟨?_, ?_⟩
  · rw [hrow]
    exact positive_series_quarterTurn U (fun x i => (C x).ofLp i) hCP
  · rw [hnorm]
    have hfirst : M*hilbertPositiveHaarNorm U (Real.sqrt 3) F +
        cubeScaleFactor U*planarC1*G*hilbertL2Norm U F ≤
      M*hilbertPositiveHaarNorm U (Real.sqrt 3) F +
        cubeScaleFactor U*planarC1*G*hilbertPositiveHaarNorm U (Real.sqrt 3) F :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hLF hcoef)
    have hsum := (hc.2.trans (add_le_add ha.2 hb.2)).trans
      (add_le_add hfirst (le_refl _))
    rw [hPF, hPR, hLR] at hsum
    convert hsum using 1 <;> ring



end
end ASDExplicitGamma.Native
