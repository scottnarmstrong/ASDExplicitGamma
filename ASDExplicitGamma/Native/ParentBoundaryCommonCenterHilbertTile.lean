module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredTrace

/-! Common-parent-center Hilbert--Schmidt row bounds on a finer observation
cube. Generalized from Inverse/PureFluxGeneratorCenteredTrace's tile proof;
all original covariance column trace constants are retained. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Model Response Triadic Variational Scalar Inverse
open scoped BigOperators
noncomputable section

local instance parentCommonHilbertTileFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The actual complete finite covariance column, centered at P but
interpolated and measured on Q. -/
def parentBoundaryCommonFiniteRawRow {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (P Q : TriadicCube 2) (j : ℕ)
    (v : H1Function (openCubeSet Q)) (x : Vec 2) : EuclideanSpace ℝ (s × Fin 2) :=
  mainEuclideanTensor (mainQ3FiniteValue e s b L x - mainQ3FiniteValue e s b L (cubeCenter P))
      (WithLp.toLp 2 ((diagInterpolant Q j v).grad x)) +
    (-((v-diagInterpolant Q j v).toFun x)) • mainQ3FiniteColumn e s b L x

/-- Genuine summability and the full common-center tile estimate. The parent
radius occurs only in the value cap; the actual observed tile controls jets. -/
theorem parent_boundary_common_center_hilbert_tile
    (P Q : TriadicCube 2) (hQP : cubeSet Q ⊆ cubeSet P) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) (s : Finset whiteBasisIndex)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q j) (b : ℝ)
    (L : {l : ℝ // 0 < l}) :
    let v := lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    MemLp (parentBoundaryCommonFiniteRawRow whiteBasis s b L P Q j v) 2
      (normalizedCubeMeasure U) ∧
    Summable (fun k => (Real.sqrt 3)^(k+1) * hilbertEnergy U
      (hilbertCubeIncrement U (k+1)
        (parentBoundaryCommonFiniteRawRow whiteBasis s b L P Q j v))) ∧
    hilbertPositiveHaarNorm U (Real.sqrt 3)
        (parentBoundaryCommonFiniteRawRow whiteBasis s b L P Q j v) ≤
      (Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) + cubeScaleFactor U * planarC1 *
          Real.sqrt ((156/5)*b^2/L.1^2)) *
          vectorPositiveHaarNorm U (diagInterpolant Q j v).grad +
        Real.sqrt ((156/5)*b^2/L.1^2) *
          positiveHaarNorm U (v-diagInterpolant Q j v).toFun +
        cubeScaleFactor U * planarC1 *
          Real.sqrt ((46488/25)*b^2/L.1^4) *
          Real.sqrt (energy U (v-diagInterpolant Q j v).toFun) := by
  intro v
  let I := diagInterpolant Q j
  let ψ := fun x => mainQ3FiniteValue whiteBasis s b L x -
    mainQ3FiniteValue whiteBasis s b L (cubeCenter P)
  let F := fun x => WithLp.toLp 2 ((I v).grad x)
  let z := v-I v
  let zU := z.restrictToOpenSubcube hU
  let C := parentBoundaryCommonFiniteRawRow whiteBasis s b L P Q j v
  have hFcoord (i : Fin 2) : MemLp (fun x => (I v).grad x i) 2
      (normalizedCubeMeasure U) :=
    memLp_on_descendant_of_memLp hU ((I v).grad_memL2_normalizedCubeMeasure i)
  have hPcoord (i : Fin 2) : Summable (fun k => (Real.sqrt 3)^(k+1) *
      energy U (cubeIncrement U (k+1) (fun x => (I v).grad x i))) :=
    diagInterpolant_gradient_summable Q j p u U hU i
  have hF : MemLp F 2 (normalizedCubeMeasure U) := by
    simpa only [F] using (memLp_piLp_iff.mpr hFcoord)
  have hPF := main_hilbert_summable_of_coordinates U hF hPcoord
  have hPHF := main_hilbertPositive_eq_vectorPositive U hFcoord hPcoord
  have hM : 0 ≤ Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) := Real.sqrt_nonneg _
  have hD : 0 ≤ Real.sqrt ((156/5:ℝ)*b^2/L.1^2) := Real.sqrt_nonneg _
  have hψbound : ∀ᵐ x ∂normalizedCubeMeasure U, ‖ψ x‖ ≤
      Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) := by
    filter_upwards [hilbert_ae_cubeSet U] with x hx
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).1
    exact (pureFluxQ3CenteredFiniteValue_norm_sq_le whiteBasis s b L P
      (hQP (cubeSet_subset_of_mem_descendantsAtDepth hU hx))).trans_eq
      (Real.sq_sqrt (by positivity)).symm
  have hψderivative : ∀ᵐ x ∂normalizedCubeMeasure U,
      (∑ i : Fin 2, ‖(fderiv ℝ ψ x) (basisVec i)‖^2) ≤
        (Real.sqrt ((156/5:ℝ)*b^2/L.1^2))^2 := by
    filter_upwards with x
    rw [Real.sq_sqrt (by positivity : 0 ≤ (156/5:ℝ)*b^2/L.1^2)]
    dsimp only [ψ]
    simp only [fderiv_sub_const]
    exact mainQ3FiniteValue_derivative_frobenius whiteBasis s b L x
  have hT := main_hilbert_tensor_product U ψ
      ((mainQ3FiniteValue_contDiff whiteBasis s b L).sub contDiff_const) hF hPF hM hD hψbound hψderivative
  have hCol := main_q3_negative_column_h1_product whiteBasis s b L U zU
  let Mcol := mainRankOneMultiplier U (mainQ3FiniteColumn whiteBasis s b L)
    (mainQ3FiniteColumn_contDiff whiteBasis s b L)
  have hBpos := Mcol.product_memLp zU.memL2_normalizedCubeMeasure
  have hB : MemLp (fun x => (-zU.toFun x) • mainQ3FiniteColumn whiteBasis s b L x)
      2 (normalizedCubeMeasure U) := by
    have hneg := hBpos.neg
    convert hneg using 1
    funext x
    simp [Mcol, mainRankOneMultiplier, neg_smul]
  let T := mainEuclideanTensorMap (κ := s) (ρ := Fin 2)
  let Aop := mainSmoothHilbertOperator U (fun x => T (ψ x))
    (T.contDiff.comp ((mainQ3FiniteValue_contDiff whiteBasis s b L).sub contDiff_const))
  have hA : MemLp (fun x => mainEuclideanTensor (ψ x) (F x)) 2
      (normalizedCubeMeasure U) := by
    change MemLp (fun x => T (ψ x) (F x)) 2 (normalizedCubeMeasure U)
    exact Aop.product_memLp hF
  have hAdd := main_hilbert_positive_add U hA hB hT.1 hCol.1
  have hL2F := main_hilbertL2_le_positive U hF hPF
  have hFirst :
      Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) * hilbertPositiveHaarNorm U (Real.sqrt 3) F +
        cubeScaleFactor U * planarC1 * Real.sqrt ((156/5)*b^2/L.1^2) *
          hilbertL2Norm U F ≤
      (Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) + cubeScaleFactor U * planarC1 *
          Real.sqrt ((156/5)*b^2/L.1^2)) *
        hilbertPositiveHaarNorm U (Real.sqrt 3) F := by
    have hc : 0 ≤ cubeScaleFactor U * planarC1 *
        Real.sqrt ((156/5:ℝ)*b^2/L.1^2) := by
      have hc1 : 0 ≤ planarC1 := by
        unfold planarC1
        exact Real.sqrt_nonneg _
      exact mul_nonneg (mul_nonneg (Triadic.cubeScaleFactor_pos' U).le hc1)
        (Real.sqrt_nonneg _)
    calc
      _ ≤ Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) * hilbertPositiveHaarNorm U (Real.sqrt 3) F +
          cubeScaleFactor U * planarC1 * Real.sqrt ((156/5)*b^2/L.1^2) *
            hilbertPositiveHaarNorm U (Real.sqrt 3) F :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hL2F hc)
      _ = _ := by ring
  have hbound : hilbertPositiveHaarNorm U (Real.sqrt 3) C ≤
      hilbertPositiveHaarNorm U (Real.sqrt 3)
          (fun x => mainEuclideanTensor (ψ x) (F x)) +
        hilbertPositiveHaarNorm U (Real.sqrt 3)
          (fun x => (-zU.toFun x) • mainQ3FiniteColumn whiteBasis s b L x) := by
    change hilbertPositiveHaarNorm U (Real.sqrt 3)
        (fun x => mainEuclideanTensor (ψ x) (F x) +
          (-zU.toFun x) • mainQ3FiniteColumn whiteBasis s b L x) ≤ _
    exact hAdd.2
  refine ⟨hA.add hB, hAdd.1, ?_⟩
  have hbound' : hilbertPositiveHaarNorm U (Real.sqrt 3) C ≤
      (Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) + cubeScaleFactor U * planarC1 *
          Real.sqrt ((156/5)*b^2/L.1^2)) *
          hilbertPositiveHaarNorm U (Real.sqrt 3) F +
        Real.sqrt ((156/5)*b^2/L.1^2) * positiveHaarNorm U zU.toFun +
        cubeScaleFactor U * planarC1 *
          Real.sqrt ((46488/25)*b^2/L.1^4) * Real.sqrt (energy U zU.toFun) := by
    calc
      _ ≤ hilbertPositiveHaarNorm U (Real.sqrt 3)
            (fun x => mainEuclideanTensor (ψ x) (F x)) +
          hilbertPositiveHaarNorm U (Real.sqrt 3)
            (fun x => (-zU.toFun x) • mainQ3FiniteColumn whiteBasis s b L x) := hbound
      _ ≤ (Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor P/L.1)^2) + cubeScaleFactor U * planarC1 *
            Real.sqrt ((156/5)*b^2/L.1^2)) *
            hilbertPositiveHaarNorm U (Real.sqrt 3) F +
          (Real.sqrt ((156/5)*b^2/L.1^2) * positiveHaarNorm U zU.toFun +
            cubeScaleFactor U * planarC1 *
              Real.sqrt ((46488/25)*b^2/L.1^4) * Real.sqrt (energy U zU.toFun)) :=
        add_le_add (hT.2.trans hFirst) hCol.2
      _ = _ := by ring
  have heqZ : zU.toFun = (v-I v).toFun := rfl
  rw [hPHF] at hbound'
  simpa only [C, F, ψ, z, zU, heqZ,
    hilbertPositiveHaarNorm, hilbertL2Norm, hilbertPrimalEnergy_real,
    hilbertEnergy_real] using hbound'

end
end ASDExplicitGamma.Native
