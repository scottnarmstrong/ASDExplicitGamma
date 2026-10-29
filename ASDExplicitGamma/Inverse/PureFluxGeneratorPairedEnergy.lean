module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorTiledProjected

/-! The common-history paired coercivity estimate on the actual source mesh. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

private theorem pureFlux_inverseHistory_sqrt_three_le_quarter (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    compatibleInverseHistory Q a ≤ lemmaVInverseHistory Q a ((3:ℝ)^(1/4:ℝ)) := by
  have hq : 1 < Real.sqrt 3 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3:ℝ)]
  have hquarter : 1 < (3:ℝ)^(1/4:ℝ) := Real.one_lt_rpow (by norm_num) (by norm_num)
  have hcomp : (3:ℝ)^(1/4:ℝ) ≤ Real.sqrt 3 := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  exact lemmaVInverseHistory_le_of_inverse_discount Q hEll hq hquarter
    ((inv_le_inv₀ (by positivity) (by positivity)).mpr hcomp)

theorem pureFlux_paired_tiled_energy_bound (Q : TriadicCube 2) (m : ℕ)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (u : AHarmonicFunction a (openCubeSet Q))
    (v : AHarmonicFunction (adjointCoeffField a) (openCubeSet Q)) (B : ℝ)
    (hhist : ∀ R ∈ descendantsAtDepth Q m,
      lemmaVInverseHistory R a ((3:ℝ)^(1/4:ℝ)) ≤ B) :
    lemmaVTiledWeakEnergy Q m (compatiblePairFirst u v) +
      lemmaVTiledWeakEnergy Q m (compatiblePairSecondImage u v) ≤
      B * blockPairingAverage (openCubeSet Q) a (compatiblePairState u v)
        (compatiblePairState u v) := by
  letI pureFluxPairedParentFiniteMeasure : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let W := compatiblePairState u v
  have hlocal (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q m) :
      vectorWeakHaarEnergy R (compatiblePairFirst u v) +
        vectorWeakHaarEnergy R (compatiblePairSecondImage u v) ≤
      B*cubeAverage R (blockPairingIntegrand a W W) := by
    letI pureFluxPairedCellFiniteMeasure : IsFiniteMeasure (volumeMeasureOn (openCubeSet R)) :=
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllR := hEll.mono (measurableSet_openCubeSet R) hsub
    let uR := u.restrictOfIsEllipticFieldOn (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hsub hEllR
    let vR := v.restrictOfIsEllipticFieldOn (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hsub
      (isEllipticFieldOn_adjointCoeffField hEllR)
    have hp := paired_compatible_coercivity R hEllR uR vR
    have hE : blockPairingAverage (openCubeSet R) a (compatiblePairState uR vR)
        (compatiblePairState uR vR) = cubeAverage R (blockPairingIntegrand a W W) := by
      rw [cubeAverage_eq_integralAverage_openCubeSet]
      rfl
    have hH : compatibleInverseHistory R a ≤ B :=
      (pureFlux_inverseHistory_sqrt_three_le_quarter R hEllR).trans (hhist R hR)
    have hEn := compatible_blockPairingAverage_nonneg hEllR (compatiblePairState uR vR)
    have hh := hp.trans (mul_le_mul_of_nonneg_right hH hEn)
    rw [hE] at hh
    exact hh
  have hmem : MemBlockL2 (openCubeSet Q) W.eval :=
    blockResponse_memBlockL2_of_mem_responseSpace_of_integrabilityData
      (blockResponse_pair_half_mem_responseSpace_of_isEllipticFieldOn a hEll u v)
      (blockResponseIntegrabilityData_pair_half_of_isEllipticFieldOn hEll u v)
  have hint := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hmem hmem hEll
  have heq : descendantsAverage Q m (fun R => cubeAverage R (blockPairingIntegrand a W W)) =
      blockPairingAverage (openCubeSet Q) a W W := by
    rw [← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q m _
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hint)]
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    rfl
  rw [← heq]
  unfold lemmaVTiledWeakEnergy descendantsAverage
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlocal)
    (show 0 ≤ ((descendantsAtDepth Q m).card:ℝ)⁻¹ by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  nlinarith only [hh]

end
end ASDExplicitGamma.Inverse
