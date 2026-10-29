module

public import ASDExplicitGamma.Variational.PairedBessel
public import ASDExplicitGamma.Scalar.SmoothFeedbackResponseSpace
public import ASDExplicitGamma.Scalar.ResidualProjectionEnergy

/-! The paired first/reciprocal mean budget for the actual homogeneous
comparison fields. Both components share one physical energy payment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Triadic Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Euclidean paired Bessel on a physical cell. No separate first/reciprocal
energy payment or rotational half is assumed. -/
theorem old_hessian_paired_response_mean (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2) (hW : BlockResponseSpace a (openCubeSet Q) W)
    (hmem : MemBlockL2 (openCubeSet Q) W.eval) :
    vecNormSq (pairedPotentialMean (openCubeSet Q) W)+
      vecNormSq (pairedFluxImageMean (openCubeSet Q) a W) ≤
        Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet Q) a)*
          blockPairingAverage (openCubeSet Q) a W W := by
  let D := (coarseBlockMatrix (openCubeSet Q) a).lowerRight
  have hv : 0<(volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  obtain ⟨_,hCoarse,_,_,_,_,hDpos,_⟩ :=
    exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet Q) hEll hv
  have hD : D.PosDef := by
    rw [show D=(coarseBlockMatrix (openCubeSet Q) a).lowerRight by rfl,
      coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    exact hDpos
  have hleft (x : Vec 2) : matVecMul D (matVecMul D⁻¹ x)=x := by
    rw [matVecMul_mul,Matrix.mul_nonsing_inv D ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit)]
    funext i
    simp [matVecMul,Matrix.one_apply]
  have hp := Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    hD.posSemidef hleft (pairedPotentialMean (openCubeSet Q) W)
  have hg := Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    hD.posSemidef hleft (pairedFluxImageMean (openCubeSet Q) a W)
  have hb := mul_le_mul_of_nonneg_left (pairedBessel_openCubeSet hEll W hW hmem)
    (Book.Ch02.matrixNorm_nonneg D)
  rw [←coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
  change _ ≤ Book.Ch02.matrixNorm D*_
  linarith only [hp,hg,hb]

/-- Both actual projected components are bounded at every descendant depth
by the same inverse maximum times one full physical energy. -/
theorem old_hessian_paired_response_projection (Q : TriadicCube 2) (depth : ℕ)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2) (hW : BlockResponseSpace a (openCubeSet Q) W)
    (hmem : MemBlockL2 (openCubeSet Q) W.eval) :
    (∑ i : Fin 2,energy Q (cubeProjection Q depth (fun x => W.potential x i)))+
      (∑ i : Fin 2,energy Q (cubeProjection Q depth (fun x =>
        (blockMatVecMul (blockCoeffField a x) (W.eval x)).2 i))) ≤
      lemmaVInverseDepthMax Q a depth*blockPairingAverage (openCubeSet Q) a W W := by
  let G := fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2
  have hpmem := memVectorL2_fst_of_memBlockL2 hmem
  have hgmem : MemVectorL2 (openCubeSet Q) G :=
    blockResponse_lowerImage_memVectorL2_of_flux_memVectorL2_of_mem_responseSpace_of_isEllipticFieldOn
      hW (memVectorL2_snd_of_memBlockL2 hmem) hEll
  rw [vector_projection_energy_eq_means Q depth W.potential
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hpmem i)),
    vector_projection_energy_eq_means Q depth G
    (fun i => memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hgmem i)),
    ←descendantsAverage_add]
  have hlocal (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q depth) :
      vecNormSq (fun i => cubeAverage R (fun x => W.potential x i))+
      vecNormSq (fun i => cubeAverage R (fun x => G x i)) ≤
        lemmaVInverseDepthMax Q a depth*blockPairingAverage (openCubeSet R) a W W := by
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let hER := hEll.mono (measurableSet_openCubeSet R) hsub
    have hh := old_hessian_paired_response_mean R hER W
      (blockResponseSpace_restrict_subcube Q R hsub a hEll W hW hmem)
      (hmem.mono_measure (Measure.restrict_mono_set volume hsub))
    have hp : pairedPotentialMean (openCubeSet R) W=
        fun i => cubeAverage R (fun x => W.potential x i) := by
      funext i
      simp only [pairedPotentialMean,volumeAverageVec,cubeAverage_eq_integralAverage_openCubeSet,
        volumeAverage,integralAverage]
    have hg : pairedFluxImageMean (openCubeSet R) a W=
        fun i => cubeAverage R (fun x => G x i) := by
      funext i
      simp only [pairedFluxImageMean,volumeAverageVec,cubeAverage_eq_integralAverage_openCubeSet,
        volumeAverage,integralAverage,G]
    rw [hp,hg] at hh
    have hmax : Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) a) ≤
        lemmaVInverseDepthMax Q a depth := by
      unfold lemmaVInverseDepthMax Book.Ch02.finsetSupReal
      exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨R,hR,rfl⟩
    exact hh.trans (mul_le_mul_of_nonneg_right hmax (compatible_blockPairingAverage_nonneg hER W))
  have hint := blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn hmem hmem hEll
  have he : descendantsAverage Q depth (fun R => blockPairingAverage (openCubeSet R) a W W)=
      blockPairingAverage (openCubeSet Q) a W W := by
    change descendantsAverage Q depth (fun R => integralAverage (openCubeSet R)
      (blockPairingIntegrand a W W))=integralAverage (openCubeSet Q) (blockPairingIntegrand a W W)
    simp_rw [←cubeAverage_eq_integralAverage_openCubeSet]
    exact (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q depth _
      (integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hint)).symm
  exact (descendantsAverage_le hlocal).trans_eq (by rw [descendantsAverage_mul_left,he])

end
end ASDExplicitGamma.Scalar
