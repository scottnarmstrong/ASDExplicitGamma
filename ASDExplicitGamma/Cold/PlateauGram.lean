module

public import ASDExplicitGamma.Cold.CoarseGramQuadratic

/-! # CO-PLATEAU-P3: the actual response Gram bound -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators RealInnerProductSpace
namespace ASDExplicitGamma.Cold

/-- The ordinary spatial mean of the actual harmonic flux/gradient graph. -/
def coarseGraphMean (Q : TriadicCube 2) {a : CoeffField 2}
    (w : AHarmonicFunction a (openCubeSet Q)) : BlockVec 2 :=
  ((fun i => volumeAverage (openCubeSet Q) (fun x => matVecMul (a x) (w.toH1.grad x) i)),
   (fun i => volumeAverage (openCubeSet Q) (fun x => w.toH1.grad x i)))

/-- CO-PLATEAU-P3. The source Gram estimate for every actual harmonic function, with the
actual response matrix and actual Euclidean operator defect. Coarse duality, positivity,
and the quadratic-response representation are derived internally from source ellipticity. -/
theorem plateau_gram (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam η : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (hη : 0 < η)
    (w : AHarmonicFunction a (openCubeSet Q)) :
    blockVecDot (coarseGraphMean Q w) (coarseGraphMean Q w) ≤
      (2*(1+η)+(2+1/(4*η))*matrixGramDefect
        (toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)) coarseGramSwap) *
      volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a w) := by
  let P := coarseGraphMean Q w
  let A := toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)
  let C := 2*(1+η)+(2+1/(4*η))*matrixGramDefect A coarseGramSwap
  let E := volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a w)
  let N := blockVecDot P P
  have hE : 0 ≤ E := volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
    (openCubeSet Q) a hEll w
  have hN : 0 ≤ N := by
    unfold N blockVecDot vecDot
    exact add_nonneg (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
      (Finset.sum_nonneg fun _ _ => mul_self_nonneg _)
  have hC : 0 ≤ C := by
    dsimp [C, matrixGramDefect]
    positivity
  have hne : (openCubeSet Q).Nonempty := by
    by_contra h
    have he := Set.not_nonempty_iff_eq_empty.mp h
    have hv : 0 < (volume (openCubeSet Q)).toReal := by
      rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
      exact cubeVolume_pos Q
    rw [he] at hv
    simp at hv
  obtain ⟨v⟩ := ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain
    hne
    (isOpenBoundedConvexDomain_openCubeSet Q) hEll (-P.1) P.2
  have hcs := basic_cg_identities_linear_response_sq_of_isResponseMaximizer_of_isEllipticFieldOn
    (openCubeSet Q) a hEll (-P.1) P.2 (v : AHarmonicFunction a (openCubeSet Q))
    v.isResponseMaximizer w
  rw [basic_cg_identities_average_pairing_eq_vecDot_average_gradient_sub_average_flux_of_isEllipticFieldOn
    (openCubeSet Q) a hEll] at hcs
  change (vecDot P.2 P.2 - vecDot (-P.1) P.1)^2 ≤ E * (2*ResponseJ (openCubeSet Q) (-P.1) P.2 a) at hcs
  have hn : vecDot P.2 P.2 - vecDot (-P.1) P.1 = N := by
    dsimp [N,blockVecDot]
    rw [vecDot_neg_left]
    ring
  rw [hn] at hcs
  let x : EuclideanSpace ℝ (BlockCoord 2) := WithLp.toLp 2 (toFullBlockVec P)
  have hj : 2*ResponseJ (openCubeSet Q) (-P.1) P.2 a =
      ⟪x,A.toEuclideanLin x + coarseGramSwap.toEuclideanLin x⟫ := by
    rw [coarse_square_response_quadratic Q hEll]
    simp only [neg_neg,vecDot_neg_left]
    rw [inner_add_right]
    change _ = ⟪x,(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) A x⟫ +
      ⟪x,(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := BlockCoord 2)) coarseGramSwap x⟫
    rw [matrix_euclidean_inner, matrix_euclidean_inner]
    change _ = (toFullBlockVec P) ⬝ᵥ (A.mulVec (toFullBlockVec P)) +
      (toFullBlockVec P) ⬝ᵥ (coarseGramSwap.mulVec (toFullBlockVec P))
    rw [coarseGramSwap_mulVec, ← toFullBlockVec_blockMatVecMul,
      dotProduct_toFullBlockVec, dotProduct_toFullBlockVec]
    simp only [blockVecDot, vecDot_comm P.2 P.1]
    ring
  have hxx : ⟪x,x⟫ = N := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (star (toFullBlockVec P)) ⬝ᵥ (toFullBlockVec P) = N
    rw [star_trivial, dotProduct_toFullBlockVec]
  have hbound := coarse_square_gram_quadratic_le Q hEll hη x
  change _ ≤ C*⟪x,x⟫ at hbound
  rw [hxx, ← hj] at hbound
  have hsq := hcs.trans (mul_le_mul_of_nonneg_left hbound hE)
  change N ≤ C*E
  by_cases hz : N = 0
  · rw [hz]
    exact mul_nonneg hC hE
  · apply le_of_mul_le_mul_right (b := N) _ (lt_of_le_of_ne hN (Ne.symm hz))
    nlinarith only [hsq]


/-- The source trace-defect version, using precisely its stated bound `η_V ≤ T(V)`. -/
theorem plateau_gram_of_defect_le (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam η T : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (hη : 0 < η)
    (hT : matrixGramDefect (toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)) coarseGramSwap ≤ T)
    (w : AHarmonicFunction a (openCubeSet Q)) :
    blockVecDot (coarseGraphMean Q w) (coarseGraphMean Q w) ≤
      (2*(1+η)+(2+1/(4*η))*T) * volumeAverage (openCubeSet Q) (scalarVariationEnergyIntegrand a w) := by
  refine (plateau_gram Q hEll hη w).trans ?_
  exact mul_le_mul_of_nonneg_right
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hT
      (show (0 : ℝ) ≤ 2+1/(4*η) by positivity)))
    (volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (openCubeSet Q) a hEll w)

end ASDExplicitGamma.Cold
