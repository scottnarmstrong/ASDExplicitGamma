module

public import ASDExplicitGamma.Scalar.SmoothFeedbackPairedBessel
public import ASDExplicitGamma.Variational.CompatibleCoercivity
public import ASDExplicitGamma.Cold.SquarePartitionProjection
public import ASDExplicitGamma.Scalar.InverseHistoryBlocks

/-! Fixed-depth projection control for the actual OLD smooth-feedback fields. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

private theorem cubeAverage_sub (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => f x - g x) = cubeAverage Q f - cubeAverage Q g := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num))

private theorem cubeAverage_congr_ae' (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hfg : f =ᵐ[volumeMeasureOn (openCubeSet Q)] g) :
    cubeAverage Q f = cubeAverage Q g := by
  rw [cubeAverage_eq_integralAverage_openCubeSet,
    cubeAverage_eq_integralAverage_openCubeSet]
  unfold integralAverage
  congr 1
  exact integral_congr_ae hfg

private theorem smooth_feedback_local_top_mean
    (M : ABKModel 2) (m : ℤ) (Q R : TriadicCube 2)
    (hRQ : openCubeSet R ⊆ openCubeSet Q) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (i : Fin 2) :
    cubeAverage R (fun x =>
      (oldSignedCellResidual Q R hRQ M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar M m).property (oldCutoffSkewCoefficient m Q ω)
        (fun _ => ((e, 0) : BlockVec 2)) (memLp_const (e, 0)) x).1 i) = e i := by
  let k := oldCutoffSkewCoefficient m Q ω
  let P : BlockVec 2 := (e, 0)
  let F : Vec 2 → BlockVec 2 := fun _ => P
  let T := oldSignedCellResidual Q R hRQ M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar M m).property k F (memLp_const P)
  have hTmem : MemBlockL2 (openCubeSet R) T := T.property
  have hRemoved := old_signed_cell_removed_variation Q R hRQ M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar M m).property k F (memLp_const P)
  have hPotential : IsPotentialZeroTraceOn (openCubeSet R)
      (fun x => P.1 - (T x).1) := by
    simpa [F, T, BlockState.eval] using hRemoved.2.1
  have hIntegral := IsPotentialZeroTraceOn.integral_eq_zero hPotential
  have hzero : cubeAverage R (fun x => P.1 i - (T x).1 i) = 0 := by
    rw [← Cold.square_volumeAverage_eq_cubeAverage]
    apply volumeAverage_eq_zero_of_integral_eq_zero
    exact congrFun hIntegral i
  have hTcoord : MemLp (fun x => (T x).1 i) 2 (normalizedCubeMeasure R) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2
        (memVectorL2_fst_of_memBlockL2 hTmem) i)
  have hconst : MemLp (fun _ : Vec 2 => P.1 i) 2 (normalizedCubeMeasure R) :=
    memLp_const (P.1 i)
  have hsub := cubeAverage_sub R hconst hTcoord
  change cubeAverage R (fun x => P.1 i - (T x).1 i) = 0 at hzero
  rw [hsub, cubeAverage_const] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- The level-depth projection of the actual affine-top defect is bounded by
the exact D3 patch energy. The proof applies compatible coercivity to the
parent minimizer minus its actual finite patch of child minimizers; the child
affine means cancel exactly. -/
theorem smooth_feedback_top_projection_le_patch_energy
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    (∑ i, energy Q (cubeProjection Q depth (fun x =>
      smoothFeedbackCellAffineTopDefect M m Q e ω x i))) ≤
      lemmaVInverseDepthMax Q
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω)) depth *
      oldSignedEnergyPairing Q M.nu (Annealed.sigmaBar M m : ℝ)
        (oldCutoffSkewCoefficient m Q ω)
        (fun x => smoothFeedbackCellAffineResidual M m Q e ω x -
          oldSignedLocalResidual Q depth M.nu (Annealed.sigmaBar M m : ℝ)
            M.nu_pos (Annealed.sigmaBar M m).property
            (oldCutoffSkewCoefficient m Q ω)
            (fun _ => ((e, 0) : BlockVec 2)) (memLp_const (e, 0)) x)
        (fun x => smoothFeedbackCellAffineResidual M m Q e ω x -
          oldSignedLocalResidual Q depth M.nu (Annealed.sigmaBar M m : ℝ)
            M.nu_pos (Annealed.sigmaBar M m).property
            (oldCutoffSkewCoefficient m Q ω)
            (fun _ => ((e, 0) : BlockVec 2)) (memLp_const (e, 0)) x) := by
  classical
  let k := oldCutoffSkewCoefficient m Q ω
  let σ := (Annealed.sigmaBar M m : ℝ)
  let a := responseFramePlanarCoefficientField M.nu σ k
  let P : BlockVec 2 := (e, 0)
  let S : Vec 2 → BlockVec 2 := smoothFeedbackCellAffineResidual M m Q e ω
  let L : Vec 2 → BlockVec 2 := oldSignedLocalResidual Q depth M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k (fun _ => P) (memLp_const P)
  let D : Vec 2 → BlockVec 2 := fun x => S x - L x
  let W : BlockState 2 := ⟨fun x => (D x).1, fun x => (D x).2⟩
  have hS : MemBlockL2 (openCubeSet Q) S := by
    simpa [S, smoothFeedbackCellAffineResidual, a, k, σ] using
      scalar_cell_response_test_memL2 Q a
        (responseFramePlanarCoefficientField_isElliptic
          (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
          (Annealed.sigmaBar M m).property k) P
  have hL : MemBlockL2 (openCubeSet Q) L :=
    old_signed_local_residual_memLp Q depth M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k (fun _ => P) (memLp_const P)
  have hD : MemBlockL2 (openCubeSet Q) D := hS.sub hL
  have hParentVar : ScalarVariation (openCubeSet Q) (fun x => S x - P) := by
    simpa [S, P, smoothFeedbackCellAffineResidual, a, k, σ] using
      scalar_cell_response_test_variation Q a
        (responseFramePlanarCoefficientField_isElliptic
          (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
          (Annealed.sigmaBar M m).property k) P
  have hPatchVar := old_signed_local_removed_variation Q depth M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k (fun _ => P) (memLp_const P)
  have hDVar : ScalarVariation (openCubeSet Q) D := by
    have hsum := scalar_variation_add hParentVar hPatchVar
    have hfields : (fun x => (S x - P) + (P - L x)) = D := by
      funext x
      change (S x - P) + (P - L x) = S x - L x
      ext j <;> simp [sub_eq_add_neg]
    exact old_signed_scalar_variation_congr_ae
      (ae_of_all (volumeMeasureOn (openCubeSet Q)) fun x => congrFun hfields x) hsum
  have hCompat := scalar_variation_compatible hDVar
  have hWpot : IsBlockPotentialOn (openCubeSet Q) W := hCompat.2.1
  have hWsol : IsBlockSolenoidalOn (openCubeSet Q) W := hCompat.2.2
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k
  have hProjected := compatible_projectionEnergy_bound hEll W hWpot hWsol hD depth
  have hScoord (i : Fin 2) : MemLp (fun x => (S x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hS) i)
  have hLcoord (i : Fin 2) : MemLp (fun x => (L x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hL) i)
  have hPcoord (i : Fin 2) : MemLp (fun _ : Vec 2 => P.1 i) 2
      (normalizedCubeMeasure Q) := memLp_const (P.1 i)
  have hSPcoord (i : Fin 2) : MemLp (fun x => (S x).1 i - P.1 i) 2
      (normalizedCubeMeasure Q) := (hScoord i).sub (hPcoord i)
  have hPLcoord (i : Fin 2) : MemLp (fun x => P.1 i - (L x).1 i) 2
      (normalizedCubeMeasure Q) := (hPcoord i).sub (hLcoord i)
  have hLocalMean (i : Fin 2) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q depth) :
      cubeAverage R (fun x => (L x).1 i) = P.1 i := by
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let Z := oldSignedCellResidual Q R hRQ M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k (fun _ => P) (memLp_const P)
    have hmeanZ : cubeAverage R (fun x => (Z x).1 i) = P.1 i := by
      simpa [Z, P, k, σ] using
        smooth_feedback_local_top_mean M m Q R hRQ e ω i
    have hRestr := old_signed_local_residual_restrict Q depth M.nu σ
      M.nu_pos (Annealed.sigmaBar M m).property k (fun _ => P) (memLp_const P) R hR
    have hAvg : cubeAverage R (fun x => (L x).1 i) =
        cubeAverage R (fun x => (Z x).1 i) := by
      apply cubeAverage_congr_ae' R
      exact hRestr.mono fun x hx => congrArg (fun z : BlockVec 2 => z.1 i) hx
    exact hAvg.trans hmeanZ
  have hPLproj (i : Fin 2) :
      cubeProjection Q depth (fun x => P.1 i - (L x).1 i) = 0 := by
    funext x
    by_cases hx : x ∈ cubeSet Q
    · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet depth hx
      rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR]
      have hmean := hLocalMean i R hR
      have hsub := cubeAverage_sub R
        (memLp_const (P.1 i))
        (memLp_normalized_of_memL2On
          (memScalarL2_coord_of_memVectorL2
            (memVectorL2_fst_of_memBlockL2
              (hL.mono_measure (Measure.restrict_mono_set volume
                (openCubeSet_subset_of_mem_descendantsAtDepth hR)))) i))
      rw [hsub, cubeAverage_const, hmean]
      simp
    · exact cubeProjection_eq_zero_of_not_mem_cubeSet Q depth _ hx
  have hProjAdd (i : Fin 2) :
      cubeProjection Q depth (fun x => (D x).1 i) =
        cubeProjection Q depth (fun x => (S x).1 i - P.1 i) := by
    have hdecomp : (fun x => (D x).1 i) =
        (fun x => ((S x).1 i - P.1 i) + (P.1 i - (L x).1 i)) := by
      funext x
      change (S x).1 i - (L x).1 i = _
      ring
    calc
      cubeProjection Q depth (fun x => (D x).1 i) =
          cubeProjection Q depth
            (fun x => ((S x).1 i - P.1 i) + (P.1 i - (L x).1 i)) := by rw [hdecomp]
      _ = cubeProjection Q depth (fun x => (S x).1 i - P.1 i) +
            cubeProjection Q depth (fun x => P.1 i - (L x).1 i) :=
          projection_add Q depth (hSPcoord i) (hPLcoord i)
      _ = _ := by rw [hPLproj i]; simp
  have hTopAE : smoothFeedbackCellAffineTopDefect M m Q e ω =ᵐ[
      volumeMeasureOn (openCubeSet Q)] (fun x => (S x).1 - e) := by
    rfl
  have hTopProjection := smooth_feedback_vector_projected_energy_congr_ae
    Q depth hTopAE
  have hProjEnergyEq :
      (∑ i, energy Q (cubeProjection Q depth (fun x =>
        smoothFeedbackCellAffineTopDefect M m Q e ω x i))) =
      ∑ i, energy Q (cubeProjection Q depth (fun x => (D x).1 i)) := by
    rw [hTopProjection]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (energy Q) (hProjAdd i).symm
  have hAverage : cubeAverage Q (blockPairingIntegrand a W W) =
      oldSignedEnergyPairing Q M.nu σ k D D := by
    rw [cubeAverage_eq_integralAverage_openCubeSet]
    rfl
  calc
    _ = ∑ i, energy Q (cubeProjection Q depth (fun x => (D x).1 i)) := hProjEnergyEq
    _ ≤ lemmaVInverseDepthMax Q a depth *
        cubeAverage Q (blockPairingIntegrand a W W) := hProjected
    _ = lemmaVInverseDepthMax Q a depth * oldSignedEnergyPairing Q M.nu σ k D D := by
      rw [hAverage]

/-- The actual reciprocal-gradient mean on one depth-j descendant is bounded
by that descendant's complementary-patch energy, multiplied by the exact
lower-right response maximum at depth j. -/
theorem smooth_feedback_descendant_reciprocal_mean_le_complementary_energy
    (M : ABKModel 2) (m : ℤ) (Q R : TriadicCube 2) (depth : ℕ)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2)
    (hR : R ∈ descendantsAtDepth Q depth) :
    let k := oldCutoffSkewCoefficient m Q ω
    let σ := (Annealed.sigmaBar M m : ℝ)
    let a := responseFramePlanarCoefficientField M.nu σ k
    let hEll := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
        (Annealed.sigmaBar M m).property k
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let Pbot : BlockVec 2 := (0, e)
    let T := oldSignedCellResidual Q R hRQ M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k (fun _ => Pbot) (memLp_const Pbot)
    let Tstate : BlockState 2 := ⟨fun x => (T x).1, fun x => (T x).2⟩
    let Z := scalarCellResponseTest Q a hEll (e, 0) +
      (-1 : ℝ) • pairedReflectState a Tstate
    vecNormSq (volumeAverageVec (openCubeSet R)
      (smoothFeedbackCellAffineReciprocalGradient M m Q e ω)) ≤
      lemmaVInverseDepthMax Q a depth *
        blockPairingAverage (openCubeSet R) a Z Z := by
  classical
  dsimp only
  let k := oldCutoffSkewCoefficient m Q ω
  let σ := (Annealed.sigmaBar M m : ℝ)
  let a := responseFramePlanarCoefficientField M.nu σ k
  let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k
  let hEllR := hEll.mono (measurableSet_openCubeSet R) hRQ
  let Ptop : BlockVec 2 := (e, 0)
  let Pbot : BlockVec 2 := (0, e)
  let T := oldSignedCellResidual Q R hRQ M.nu
    (Annealed.sigmaBar M m : ℝ) M.nu_pos
    (Annealed.sigmaBar M m).property k (fun _ => Pbot) (memLp_const Pbot)
  let Tstate : BlockState 2 := ⟨fun x => (T x).1, fun x => (T x).2⟩
  let S := scalarCellResponseTest Q a hEll Ptop
  let Z := S + (-1 : ℝ) • pairedReflectState a Tstate
  let D := (coarseBlockMatrix (openCubeSet R) a).lowerRight
  let p := volumeAverageVec (openCubeSet R)
    (smoothFeedbackCellAffineReciprocalGradient M m Q e ω)
  have hvol : 0 < (volume (openCubeSet R)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos R
  obtain ⟨_, hCoarse, _, _, _, _, hDpositive, _⟩ :=
    exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet R)
      hEllR hvol
  have hDpos : D.PosDef := by
    change (coarseBlockMatrix (openCubeSet R) a).lowerRight.PosDef
    rw [coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    exact hDpositive
  have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDpos.isUnit
  have hDleft : ∀ ξ : Vec 2, matVecMul D (matVecMul D⁻¹ ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hDdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hMetric :=
    Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
      hDpos.posSemidef hDleft p
  have hDopen : sigmaStarInvCoarse (openCubeSet R) a = D := by
    rw [inverse_history_lowerRight R a hEllR, cube_coarseMatrix_eq_open]
  have hDmax : Book.Ch02.matrixNorm D ≤ lemmaVInverseDepthMax Q a depth := by
    rw [← hDopen]
    unfold lemmaVInverseDepthMax Book.Ch02.finsetSupReal
    exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨R, hR, rfl⟩
  have hQuadNonneg : 0 ≤ vecDot p (matVecMul D⁻¹ p) := by
    have h := hDpos.inv.posSemidef.dotProduct_mulVec_nonneg p
    simpa only [star_trivial, vecDot, matVecMul, Matrix.mulVec, dotProduct] using h
  have hBessel := smooth_feedback_descendant_top_complementary_paired_bessel
    M m Q depth e ω R hR
  have hMean : pairedFluxImageMean (openCubeSet R) a Z = p := by
    simpa [k, σ, a, hRQ, Ptop, Pbot, T, Tstate, S, Z, p] using hBessel.2.2
  have hBesselEnergy : vecDot p (matVecMul D⁻¹ p) ≤
      blockPairingAverage (openCubeSet R) a Z Z := by
    rw [← hMean]
    simpa [k, σ, a, hRQ, Ptop, Pbot, T, Tstate, S, Z, D] using hBessel.2.1
  have hMaxNonneg := lemmaVInverseDepthMax_nonneg Q a depth
  calc
    vecNormSq p ≤ Book.Ch02.matrixNorm D * vecDot p (matVecMul D⁻¹ p) := hMetric
    _ ≤ lemmaVInverseDepthMax Q a depth * vecDot p (matVecMul D⁻¹ p) :=
      mul_le_mul_of_nonneg_right hDmax hQuadNonneg
    _ ≤ lemmaVInverseDepthMax Q a depth * blockPairingAverage (openCubeSet R) a Z Z :=
      mul_le_mul_of_nonneg_left hBesselEnergy hMaxNonneg

/-- The sum of coordinate projection energies at depth `j` is the average
of the squared vector means on the depth-`j` descendants. This is the
partition identity used to assemble the cellwise reciprocal estimate into
the pathwise weak-Haar bound. -/
theorem smooth_feedback_vector_projection_energy_eq_descendant_means
    (Q : TriadicCube 2) (depth : ℕ) (F : Vec 2 → Vec 2) :
    (∑ i : Fin 2, energy Q (cubeProjection Q depth (fun x => F x i))) =
      descendantsAverage Q depth (fun R =>
        vecNormSq (volumeAverageVec (openCubeSet R) F)) := by
  have hcoord (i : Fin 2) :
      energy Q (cubeProjection Q depth (fun x => F x i)) =
        descendantsAverage Q depth (fun R =>
          (cubeAverage R (fun x => F x i)) ^ 2) := by
    calc
      energy Q (cubeProjection Q depth (fun x => F x i)) =
          energy Q (cubeProjection Q (depth + 0) (fun x => F x i)) := by
            simp
      _ = descendantsAverage Q depth (fun R =>
            energy R (cubeProjection R 0 (fun x => F x i))) :=
          (descendantsAverage_localProjection_eq Q depth 0
            (fun x => F x i)).symm
      _ = descendantsAverage Q depth (fun R =>
            (cubeAverage R (fun x => F x i)) ^ 2) := by
          congr 1
          funext R
          exact energy_projection_zero R (fun x => F x i)
  calc
    (∑ i : Fin 2, energy Q (cubeProjection Q depth (fun x => F x i))) =
        ∑ i : Fin 2, descendantsAverage Q depth (fun R =>
          (cubeAverage R (fun x => F x i)) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hcoord i
    _ = descendantsAverage Q depth (fun R =>
          ∑ i : Fin 2, (cubeAverage R (fun x => F x i)) ^ 2) := by
      simpa using (descendantsAverage_sum Q depth Finset.univ
        (fun R i => (cubeAverage R (fun x => F x i)) ^ 2)).symm
    _ = descendantsAverage Q depth (fun R =>
          vecNormSq (volumeAverageVec (openCubeSet R) F)) := by
      congr 1
      funext R
      simp [vecNormSq, vecDot, volumeAverageVec,
        Cold.square_volumeAverage_eq_cubeAverage, pow_two]

/-- The reciprocal projection at depth `j` is bounded by the actual
parent-minus-reflected-patch energy, with the sharp inverse-response maximum
at that depth. The finite descendant average is identified with the parent
energy by the OLD source partition theorem. -/
theorem smooth_feedback_reciprocal_projection_le_complementary_patch
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    let k := oldCutoffSkewCoefficient m Q ω
    let σ := (Annealed.sigmaBar M m : ℝ)
    let a := responseFramePlanarCoefficientField M.nu σ k
    let Pbot : BlockVec 2 := (0, e)
    let S := smoothFeedbackCellAffineResidual M m Q e ω
    let T := oldSignedLocalResidual Q depth M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k (fun _ => Pbot) (memLp_const Pbot)
    let Tstate : BlockState 2 := ⟨fun x => (T x).1, fun x => (T x).2⟩
    let J := (pairedReflectState a Tstate).eval
    (∑ i, energy Q (cubeProjection Q depth (fun x =>
      smoothFeedbackCellAffineReciprocalGradient M m Q e ω x i))) ≤
      lemmaVInverseDepthMax Q a depth *
        oldSignedEnergyPairing Q M.nu σ k
          (fun x => S x - J x) (fun x => S x - J x) := by
  classical
  dsimp only
  let k := oldCutoffSkewCoefficient m Q ω
  let σ := (Annealed.sigmaBar M m : ℝ)
  let a := responseFramePlanarCoefficientField M.nu σ k
  let Ptop : BlockVec 2 := (e, 0)
  let Pbot : BlockVec 2 := (0, e)
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k
  let S := smoothFeedbackCellAffineResidual M m Q e ω
  let F : Vec 2 → BlockVec 2 := fun _ => Pbot
  let hF : MemBlockL2 (openCubeSet Q) F := memLp_const Pbot
  let T := oldSignedLocalResidual Q depth M.nu σ M.nu_pos
    (Annealed.sigmaBar M m).property k F hF
  let Tstate : BlockState 2 := ⟨fun x => (T x).1, fun x => (T x).2⟩
  let J := (pairedReflectState a Tstate).eval
  let W : Vec 2 → BlockVec 2 := fun x => S x - J x
  let C := lemmaVInverseDepthMax Q a depth
  let cellEnergy : Native.OldSignedCellIndex Q depth → ℝ := fun U =>
    let R := U.val
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let Tcell := oldSignedCellResidual Q R hRQ M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k F hF
    let TcellState : BlockState 2 :=
      ⟨fun x => (Tcell x).1, fun x => (Tcell x).2⟩
    let Z := scalarCellResponseTest Q a hEll Ptop +
      (-1 : ℝ) • pairedReflectState a TcellState
    blockPairingAverage (openCubeSet R) a Z Z
  have hTmem : MemBlockL2 (openCubeSet Q) T :=
    old_signed_local_residual_memLp Q depth M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k F hF
  have hJmem : MemBlockL2 (openCubeSet Q) J := by
    have hImage := scalar_coefficient_flux_memL2 Q a hEll hTmem
    change MemBlockL2 (openCubeSet Q)
      (fun x => ((scalarCoefficientFlux a T x).2, (scalarCoefficientFlux a T x).1))
    exact memBlockL2_blockField (memVectorL2_snd_of_memBlockL2 hImage)
      (memVectorL2_fst_of_memBlockL2 hImage)
  have hSmem : MemBlockL2 (openCubeSet Q) S := by
    simpa [S, smoothFeedbackCellAffineResidual, a, k, σ] using
      scalar_cell_response_test_memL2 Q a hEll Ptop
  have hWmem : MemBlockL2 (openCubeSet Q) W := hSmem.sub hJmem
  have hPartition := old_signed_energy_pairing_partition Q depth M.nu σ
    M.nu_pos (Annealed.sigmaBar M m).property k hWmem hWmem
  have hLocalEnergy (U : Native.OldSignedCellIndex Q depth) :
      cellEnergy U = oldSignedEnergyPairing U.val M.nu σ
        (oldSignedCellCoefficient Q U.val
          (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) W W := by
    let R := U.val
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth U.property
    let kR := oldSignedCellCoefficient Q R hRQ k
    let aR := responseFramePlanarCoefficientField M.nu σ kR
    let Tcell := oldSignedCellResidual Q R hRQ M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k F hF
    let TcellState : BlockState 2 :=
      ⟨fun x => (Tcell x).1, fun x => (Tcell x).2⟩
    let Z := scalarCellResponseTest Q a hEll Ptop +
      (-1 : ℝ) • pairedReflectState a TcellState
    have hRestr := old_signed_local_residual_restrict Q depth M.nu σ
      M.nu_pos (Annealed.sigmaBar M m).property k F hF R U.property
    have hRestr' : T =ᵐ[volumeMeasureOn (openCubeSet R)] Tcell := by
      simpa [T, Tcell] using hRestr
    have hTae : Tstate.eval =ᵐ[volumeMeasureOn (openCubeSet R)] Tcell := by
      filter_upwards [hRestr'] with x hx
      simpa [Tstate, BlockState.eval] using hx
    have hWae : W =ᵐ[volumeMeasureOn (openCubeSet R)] Z.eval := by
      filter_upwards [hTae] with x hx
      have hSpoint : S x =
          (scalarCellResponseTest Q a hEll Ptop).eval x := by
        rfl
      have hTpot : Tstate.potential x = (Tcell x).1 := by
        have h := congrArg Prod.fst hx
        simpa [BlockState.eval] using h
      have hTflux : Tstate.flux x = (Tcell x).2 := by
        have h := congrArg Prod.snd hx
        simpa [BlockState.eval] using h
      have hReflect : (pairedReflectState a Tstate).eval x =
          (pairedReflectState a TcellState).eval x := by
        simp only [pairedReflectState, BlockState.eval]
        rw [hTpot, hTflux]
      change S x - (pairedReflectState a Tstate).eval x = Z.eval x
      rw [hReflect, hSpoint]
      apply Prod.ext
      · funext i
        change (scalarCellResponseTest Q a hEll Ptop).potential x i -
          (pairedReflectState a TcellState).potential x i =
          (scalarCellResponseTest Q a hEll Ptop).potential x i +
            (-1 : ℝ) * (pairedReflectState a TcellState).potential x i
        ring
      · funext i
        change (scalarCellResponseTest Q a hEll Ptop).flux x i -
          (pairedReflectState a TcellState).flux x i =
          (scalarCellResponseTest Q a hEll Ptop).flux x i +
            (-1 : ℝ) * (pairedReflectState a TcellState).flux x i
        ring
    have hCoeff : aR =ᵐ[volumeMeasureOn (openCubeSet R)] a := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      simp only [aR, a, responseFramePlanarCoefficientField]
      rw [old_signed_cell_coefficient_extension_eq Q R hRQ k hx]
    have hIntegrand :
        (fun x => blockPairingIntegrand a Z Z x) =ᵐ[
          volumeMeasureOn (openCubeSet R)]
        (fun x => blockVecDot (W x)
          (blockMatVecMul (blockCoeffField aR x) (W x))) := by
      filter_upwards [hWae, hCoeff] with x hx hcoeff
      change blockVecDot (Z.eval x)
          (blockMatVecMul (blockCoeffField a x) (Z.eval x)) =
        blockVecDot (W x)
          (blockMatVecMul (blockCoeffField aR x) (W x))
      rw [← hx]
      have hblockCoeff : blockCoeffField a x = blockCoeffField aR x := by
        change blockMatrixOfCoeff (a x) = blockMatrixOfCoeff (aR x)
        rw [← hcoeff]
      rw [hblockCoeff]
    unfold cellEnergy blockPairingAverage oldSignedEnergyPairing
      blockPairingIntegrand volumeAverage
    change (volume (openCubeSet R)).toReal⁻¹ *
        ∫ x in openCubeSet R, blockPairingIntegrand a Z Z x ∂volume = _
    rw [integral_congr_ae hIntegrand]
  have hMeanBound (U : Native.OldSignedCellIndex Q depth) :
      vecNormSq (volumeAverageVec (openCubeSet U.val)
        (smoothFeedbackCellAffineReciprocalGradient M m Q e ω)) ≤
        C * cellEnergy U := by
    have h := smooth_feedback_descendant_reciprocal_mean_le_complementary_energy
      M m Q U.val depth e ω U.property
    simpa [C, cellEnergy, k, σ, a, Ptop, Pbot, hEll, F, hF] using h
  have hAverage := Native.old_signed_cell_average_mono Q depth hMeanBound
  have hAverageEnergy :
      Native.oldSignedCellAverage Q depth cellEnergy =
        oldSignedEnergyPairing Q M.nu σ k W W := by
    calc
      Native.oldSignedCellAverage Q depth cellEnergy =
          Native.oldSignedCellAverage Q depth (fun U =>
            oldSignedEnergyPairing U.val M.nu σ
              (oldSignedCellCoefficient Q U.val
                (openCubeSet_subset_of_mem_descendantsAtDepth U.property) k) W W) := by
          apply congrArg (Native.oldSignedCellAverage Q depth)
          funext U
          exact hLocalEnergy U
      _ = oldSignedEnergyPairing Q M.nu σ k W W := hPartition.symm
  have hProjection := smooth_feedback_vector_projection_energy_eq_descendant_means
    Q depth (smoothFeedbackCellAffineReciprocalGradient M m Q e ω)
  have hMeanCell := Native.old_signed_cell_average_eq_descendantsAverage Q depth
    (fun R => vecNormSq (volumeAverageVec (openCubeSet R)
      (smoothFeedbackCellAffineReciprocalGradient M m Q e ω)))
  calc
    (∑ i, energy Q (cubeProjection Q depth (fun x =>
        smoothFeedbackCellAffineReciprocalGradient M m Q e ω x i))) =
        Native.oldSignedCellAverage Q depth (fun U =>
          vecNormSq (volumeAverageVec (openCubeSet U.val)
            (smoothFeedbackCellAffineReciprocalGradient M m Q e ω))) := by
      exact hProjection.trans hMeanCell.symm
    _ ≤ C * Native.oldSignedCellAverage Q depth cellEnergy := by
      rw [← Native.old_signed_cell_average_mul Q depth C cellEnergy]
      exact hAverage
    _ = C * oldSignedEnergyPairing Q M.nu σ k W W := by rw [hAverageEnergy]

/-- The complete fixed-depth smooth-feedback projection increment is
controlled by the sharp inverse-response maximum times the actual descendant
pair charge. The top D3 and reciprocal contributions assemble into that
charge cell by cell. -/
theorem smooth_feedback_directional_projection_depth_le_pair_charge
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    let k := oldCutoffSkewCoefficient m Q ω
    let σ := (Annealed.sigmaBar M m : ℝ)
    let a := responseFramePlanarCoefficientField M.nu σ k
    (∑ i, energy Q (cubeProjection Q depth (fun x =>
      smoothFeedbackCellAffineTopDefect M m Q e ω x i))) +
      (∑ i, energy Q (cubeProjection Q depth (fun x =>
        smoothFeedbackCellAffineReciprocalGradient M m Q e ω x i))) ≤
      lemmaVInverseDepthMax Q a depth *
        descendantsAverage Q depth (fun R =>
          smoothFeedbackPairCharge M m R e ω) := by
  classical
  dsimp only
  let k := oldCutoffSkewCoefficient m Q ω
  let σ := (Annealed.sigmaBar M m : ℝ)
  let a := responseFramePlanarCoefficientField M.nu σ k
  let Ptop : BlockVec 2 := (e, 0)
  let Pbot : BlockVec 2 := (0, e)
  let hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k
  let S := smoothFeedbackCellAffineResidual M m Q e ω
  let Ltop := oldSignedLocalResidual Q depth M.nu σ M.nu_pos
    (Annealed.sigmaBar M m).property k (fun _ => Ptop) (memLp_const Ptop)
  let Tbot := oldSignedLocalResidual Q depth M.nu σ M.nu_pos
    (Annealed.sigmaBar M m).property k (fun _ => Pbot) (memLp_const Pbot)
  let Tstate : BlockState 2 := ⟨fun x => (Tbot x).1, fun x => (Tbot x).2⟩
  let J := (pairedReflectState a Tstate).eval
  let D3 : Vec 2 → BlockVec 2 := fun x => S x - Ltop x
  let Comp : Vec 2 → BlockVec 2 := fun x => S x - J x
  let C := lemmaVInverseDepthMax Q a depth
  have hTop := smooth_feedback_top_projection_le_patch_energy
    M m Q depth e ω
  have hRec := smooth_feedback_reciprocal_projection_le_complementary_patch
    M m Q depth e ω
  have hD3 := smooth_feedback_top_patch_pythagoras M m Q depth e ω
  have hD4 := smooth_feedback_top_parent_complementary_patch_identity
    M m Q depth e ω
  have hTopBound :
      (∑ i, energy Q (cubeProjection Q depth (fun x =>
        smoothFeedbackCellAffineTopDefect M m Q e ω x i))) ≤
        C * oldSignedEnergyPairing Q M.nu σ k D3 D3 := by
    simpa [k, σ, a, Ltop, D3, S, C] using hTop
  have hRecBound :
      (∑ i, energy Q (cubeProjection Q depth (fun x =>
        smoothFeedbackCellAffineReciprocalGradient M m Q e ω x i))) ≤
        C * oldSignedEnergyPairing Q M.nu σ k Comp Comp := by
    simpa [k, σ, a, Pbot, hEll, Tbot, Tstate, J, S, Comp, C] using hRec
  have hD3' : oldSignedEnergyPairing Q M.nu σ k D3 D3 =
      descendantsAverage Q depth (fun R =>
        blockVecDot Ptop (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) a) Ptop)) -
        blockVecDot Ptop (blockMatVecMul
          (coarseBlockMatrix (openCubeSet Q) a) Ptop) := by
    simpa [k, σ, a, Ptop, S, Ltop, D3] using hD3
  have hD4' : oldSignedEnergyPairing Q M.nu σ k Comp Comp =
      blockVecDot Ptop (blockMatVecMul
          (coarseBlockMatrix (openCubeSet Q) a) Ptop) +
        descendantsAverage Q depth (fun R =>
          blockVecDot Pbot (blockMatVecMul
            (coarseBlockMatrix (openCubeSet R) a) Pbot)) -
          2 * vecNormSq e := by
    simpa [k, σ, a, Ptop, Pbot, S, Tbot, Tstate, J, Comp] using hD4
  have hCellCharge (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q depth) :
      blockVecDot Ptop (blockMatVecMul
        (coarseBlockMatrix (openCubeSet R) a) Ptop) +
        blockVecDot Pbot (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) a) Pbot) -
          2 * vecNormSq e =
        smoothFeedbackPairCharge M m R e ω := by
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let kR := oldSignedCellCoefficient Q R hRQ k
    let aR := responseFramePlanarCoefficientField M.nu σ kR
    have hCoeff : a =ᵐ[volumeMeasureOn (openCubeSet R)] aR := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      simp only [a, aR, responseFramePlanarCoefficientField]
      rw [old_signed_cell_coefficient_extension_eq Q R hRQ k hx]
    have hCellMatrix :
        coarseBlockMatrix (openCubeSet R) a =
          smoothFeedbackCellA M m R ω := by
      calc
        coarseBlockMatrix (openCubeSet R) a =
            coarseBlockMatrix (openCubeSet R) aR :=
          coarseBlockMatrix_congr_of_ae_eq hCoeff
        _ = smoothFeedbackCellA M m R ω := by
          let aCube := responseFramePlanarCoefficientField M.nu σ
            (smoothFeedbackCellCubeCoefficient m R ω)
          have hCube : coarseBlockMatrix (cubeSet R) aCube =
              smoothFeedbackCellA M m R ω := by
            have hframe := Variational.response_coarseMatrix_frame_eq
              (measurableSet_cubeSet R) M.nu σ M.nu_pos
              (Annealed.sigmaBar M m).property
              (smoothFeedbackCellCubeCoefficient m R ω)
            rw [hframe, coarseBlockMatrix_congr_of_ae_eq
              (smooth_feedback_cube_physical_coefficient M m R ω)]
            rfl
          calc
            coarseBlockMatrix (openCubeSet R) aR =
                coarseBlockMatrix (openCubeSet R) aCube :=
              coarseBlockMatrix_congr_of_ae_eq
                (smooth_feedback_open_frame_coefficients_ae M m R ω)
            _ = coarseBlockMatrix (cubeSet R) aCube :=
              (Variational.cube_coarseMatrix_eq_open R _).symm
            _ = smoothFeedbackCellA M m R ω := hCube
    rw [hCellMatrix]
    simp [Ptop, Pbot, smoothFeedbackPairCharge,
      smoothFeedbackCellK, smoothFeedbackCellD,
      blockVecDot, blockMatVecMul, matVecMul, vecDot]
  have hChargeAverage :
      descendantsAverage Q depth (fun R =>
        smoothFeedbackPairCharge M m R e ω) =
      descendantsAverage Q depth (fun R =>
        blockVecDot Ptop (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) a) Ptop) +
        blockVecDot Pbot (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) a) Pbot) -
        2 * vecNormSq e) := by
    change ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
        (descendantsAtDepth Q depth).sum (fun R =>
          smoothFeedbackPairCharge M m R e ω) =
      ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
        (descendantsAtDepth Q depth).sum (fun R =>
          blockVecDot Ptop (blockMatVecMul
            (coarseBlockMatrix (openCubeSet R) a) Ptop) +
          blockVecDot Pbot (blockMatVecMul
            (coarseBlockMatrix (openCubeSet R) a) Pbot) -
          2 * vecNormSq e)
    apply congrArg (fun z : ℝ =>
      ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * z)
    apply Finset.sum_congr rfl
    intro R hR
    exact (hCellCharge R hR).symm
  have hEnergyIdentity :
      oldSignedEnergyPairing Q M.nu σ k D3 D3 +
        oldSignedEnergyPairing Q M.nu σ k Comp Comp =
      descendantsAverage Q depth
        (fun R => smoothFeedbackPairCharge M m R e ω) := by
    rw [hD3', hD4', hChargeAverage]
    simp only [sub_eq_add_neg, descendantsAverage_add, descendantsAverage_const]
    ring
  calc
    _ ≤ C * oldSignedEnergyPairing Q M.nu σ k D3 D3 +
        C * oldSignedEnergyPairing Q M.nu σ k Comp Comp :=
      add_le_add hTopBound hRecBound
    _ = C * (oldSignedEnergyPairing Q M.nu σ k D3 D3 +
        oldSignedEnergyPairing Q M.nu σ k Comp Comp) := by ring
    _ = C * descendantsAverage Q depth
        (fun R => smoothFeedbackPairCharge M m R e ω) := by rw [hEnergyIdentity]

/-- Summing the two basis-direction pair charges gives exactly the actual
four-load trace defect on each cell. This identity preserves the sharp single
trace factor needed before applying planar isotropy. -/
theorem smooth_feedback_cell_pair_charge_basis_sum
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    (∑ e : Fin 2,
      smoothFeedbackPairCharge M m Q (basisVec e) ω) =
      smoothFeedbackCellT M m Q ω := by
  rw [smooth_feedback_cell_t_eq_block_traces]
  simp [Fin.sum_univ_two, basisVec, smoothFeedbackPairCharge,
    smoothFeedbackCellK, smoothFeedbackCellD, vecDot, matVecMul,
    vecNormSq, Matrix.trace]
  ring

/-- The sum of both input-direction fixed-depth projection energies is
bounded by one copy of the averaged cell trace excess, with no factor two. -/
theorem smooth_feedback_directional_projection_depth_basis_trace_le
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (depth : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    (∑ e : Fin 2,
      ((∑ i, energy Q (cubeProjection Q depth (fun x =>
        smoothFeedbackCellAffineTopDefect M m Q (basisVec e) ω x i))) +
        (∑ i, energy Q (cubeProjection Q depth (fun x =>
          smoothFeedbackCellAffineReciprocalGradient M m Q (basisVec e) ω x i))))) ≤
      lemmaVInverseDepthMax Q
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (oldCutoffSkewCoefficient m Q ω)) depth *
        descendantsAverage Q depth (fun R => smoothFeedbackCellT M m R ω) := by
  classical
  let a := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω)
  have hDirection (e : Fin 2) :
      (∑ i, energy Q (cubeProjection Q depth (fun x =>
        smoothFeedbackCellAffineTopDefect M m Q (basisVec e) ω x i))) +
        (∑ i, energy Q (cubeProjection Q depth (fun x =>
          smoothFeedbackCellAffineReciprocalGradient M m Q (basisVec e) ω x i))) ≤
        lemmaVInverseDepthMax Q a depth * descendantsAverage Q depth
          (fun R => smoothFeedbackPairCharge M m R (basisVec e) ω) := by
    simpa [a] using
      smooth_feedback_directional_projection_depth_le_pair_charge
        M m Q depth (basisVec e) ω
  have hsum :
      (∑ e : Fin 2,
        ((∑ i, energy Q (cubeProjection Q depth (fun x =>
          smoothFeedbackCellAffineTopDefect M m Q (basisVec e) ω x i))) +
          (∑ i, energy Q (cubeProjection Q depth (fun x =>
            smoothFeedbackCellAffineReciprocalGradient M m Q (basisVec e) ω x i))))) ≤
      ∑ e : Fin 2, lemmaVInverseDepthMax Q a depth * descendantsAverage Q depth
        (fun R => smoothFeedbackPairCharge M m R (basisVec e) ω) := by
    apply Finset.sum_le_sum
    intro e he
    exact hDirection e
  have hAverage :
      descendantsAverage Q depth (fun R =>
        ∑ e : Fin 2, smoothFeedbackPairCharge M m R (basisVec e) ω) =
      descendantsAverage Q depth (fun R => smoothFeedbackCellT M m R ω) := by
    apply congrArg (descendantsAverage Q depth)
    funext R
    exact smooth_feedback_cell_pair_charge_basis_sum M m R ω
  have hAverageSum := ASDExplicitGamma.Triadic.descendantsAverage_sum
    (Q := Q) (j := depth)
    (fun e R => smoothFeedbackPairCharge M m R (basisVec e) ω)
  calc
    _ ≤ ∑ e : Fin 2, lemmaVInverseDepthMax Q a depth *
          descendantsAverage Q depth
            (fun R => smoothFeedbackPairCharge M m R (basisVec e) ω) := hsum
    _ = lemmaVInverseDepthMax Q a depth *
        (∑ e : Fin 2, descendantsAverage Q depth
          (fun R => smoothFeedbackPairCharge M m R (basisVec e) ω)) := by
      rw [Finset.mul_sum]
    _ = lemmaVInverseDepthMax Q a depth *
        descendantsAverage Q depth (fun R =>
          ∑ e : Fin 2, smoothFeedbackPairCharge M m R (basisVec e) ω) := by
      rw [← hAverageSum]
    _ = lemmaVInverseDepthMax Q a depth *
        descendantsAverage Q depth (fun R => smoothFeedbackCellT M m R ω) := by
      rw [hAverage]

private theorem vectorWeakHaarEnergy_weighted_projection_identity
    (Q : TriadicCube 2) (F : Vec 2 → Vec 2)
    (hF : ∀ i : Fin 2, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    vectorWeakHaarEnergy Q F =
      (1 - Scalar.inverseHistoryDiscount ^ 2) *
        ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
          (∑ i : Fin 2,
            energy Q (cubeProjection Q j (fun x => F x i))) := by
  let α := Scalar.inverseHistoryDiscount
  have hq : (1 : ℝ) < Real.sqrt 3 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hBaseSq : Scalar.sourceHaarBase ^ 2 = Real.sqrt 3 := by
    rw [Scalar.sourceHaarBase, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    norm_num
  have hBaseInv : Scalar.sourceHaarBase⁻¹ = α := by
    dsimp [α]
    exact Scalar.inverse_history_discount_eq.symm
  have hInvSqrt : (Real.sqrt 3)⁻¹ = α ^ 2 := by
    have h := congrArg (fun x : ℝ => x⁻¹) hBaseSq
    rw [← inv_pow, hBaseInv] at h
    exact h.symm
  have hCoordSummable (i : Fin 2) : Summable (fun j : ℕ =>
      ((Real.sqrt 3)⁻¹) ^ j *
        energy Q (cubeProjection Q j (fun x => F x i))) :=
    summable_weighted_projections Q hq (hF i)
  have hRep : vectorWeakHaarEnergy Q F =
      (1 - (Real.sqrt 3)⁻¹) * ∑' j : ℕ,
        ((Real.sqrt 3)⁻¹) ^ j *
          (∑ i : Fin 2,
            energy Q (cubeProjection Q j (fun x => F x i))) := by
    simp_rw [vectorWeakHaarEnergy, dualEnergy_eq Q hq (hF _)]
    rw [← Finset.mul_sum,
      ← Summable.tsum_finsetSum (fun i _ => hCoordSummable i)]
    congr 1
    exact tsum_congr fun j => (Finset.mul_sum _ _ _).symm
  rw [hRep, hInvSqrt]
  congr 1
  apply tsum_congr
  intro j
  have hpow : (α ^ 2) ^ j = α ^ (2 * j) := by rw [← pow_mul]
  rw [hpow]

/-- The actual depth-`j` projection energy of the affine-top defect and
reciprocal gradient for one input direction. -/
noncomputable def smoothFeedbackCellDirectionalProjectionEnergyAtDepth
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  (∑ i, energy Q (cubeProjection Q j (fun x =>
    smoothFeedbackCellAffineTopDefect M m Q e ω x i))) +
    (∑ i, energy Q (cubeProjection Q j (fun x =>
      smoothFeedbackCellAffineReciprocalGradient M m Q e ω x i)))

/-- The actual directional affine Gram trace, defined by summing its
quadratic form over the two coordinate directions. -/
noncomputable def smoothFeedbackCellDirectionalGammaTrace
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ e : Fin 2, smoothFeedbackCellDirectionalGamma M m Q (basisVec e) ω

private theorem smooth_feedback_directional_gamma_weighted_series
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (ω : Cutoff.CutoffSample 2) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ (2 * j) *
        smoothFeedbackCellDirectionalProjectionEnergyAtDepth M m Q e ω j) ∧
      smoothFeedbackCellDirectionalGamma M m Q e ω =
        (1 - Scalar.inverseHistoryDiscount ^ 2) *
          ∑' j : ℕ, Scalar.inverseHistoryDiscount ^ (2 * j) *
            smoothFeedbackCellDirectionalProjectionEnergyAtDepth M m Q e ω j := by
  classical
  let α := Scalar.inverseHistoryDiscount
  let k := oldCutoffSkewCoefficient m Q ω
  let σ := (Annealed.sigmaBar M m : ℝ)
  let a := responseFramePlanarCoefficientField M.nu σ k
  let Ftop : Vec 2 → Vec 2 := smoothFeedbackCellAffineTopDefect M m Q e ω
  let Frecip : Vec 2 → Vec 2 := smoothFeedbackCellAffineReciprocalGradient M m Q e ω
  let Etop (j : ℕ) : ℝ :=
    ∑ i : Fin 2, energy Q (cubeProjection Q j (fun x => Ftop x i))
  let Erecip (j : ℕ) : ℝ :=
    ∑ i : Fin 2, energy Q (cubeProjection Q j (fun x => Frecip x i))
  let E (j : ℕ) : ℝ := Etop j + Erecip j
  change Summable (fun j : ℕ => α ^ (2 * j) * E j) ∧
    smoothFeedbackCellDirectionalGamma M m Q e ω =
      (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * E j
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k
  have hS : MemBlockL2 (openCubeSet Q)
      (smoothFeedbackCellAffineResidual M m Q e ω) := by
    simpa [smoothFeedbackCellAffineResidual, a, hEll, k, σ] using
      scalar_cell_response_test_memL2 Q a hEll (e, 0)
  have hSfirst (i : Fin 2) : MemLp
      (fun x => (smoothFeedbackCellAffineResidual M m Q e ω x).1 i)
      2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2
        (memVectorL2_fst_of_memBlockL2 hS) i)
  have hTopCoord (i : Fin 2) : MemLp (fun x => Ftop x i) 2
      (normalizedCubeMeasure Q) := by
    exact (hSfirst i).sub (memLp_const (e i))
  have hFlux : MemBlockL2 (openCubeSet Q)
      (fun x => scalarCoefficientFlux a
        (smoothFeedbackCellAffineResidual M m Q e ω) x) :=
    scalar_coefficient_flux_memL2 Q a hEll hS
  have hRecipCoord (i : Fin 2) : MemLp (fun x => Frecip x i) 2
      (normalizedCubeMeasure Q) := by
    simpa [Frecip, smoothFeedbackCellAffineReciprocalGradient, a, k, σ] using
      memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2
          (memVectorL2_snd_of_memBlockL2 hFlux) i)
  have hTopRep := vectorWeakHaarEnergy_weighted_projection_identity
    Q Ftop hTopCoord
  have hRecipRep := vectorWeakHaarEnergy_weighted_projection_identity
    Q Frecip hRecipCoord
  have hq : (1 : ℝ) < Real.sqrt 3 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hBaseSq : Scalar.sourceHaarBase ^ 2 = Real.sqrt 3 := by
    rw [Scalar.sourceHaarBase, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    norm_num
  have hBaseInv : Scalar.sourceHaarBase⁻¹ = α := by
    dsimp [α]
    exact Scalar.inverse_history_discount_eq.symm
  have hInvSqrt : (Real.sqrt 3)⁻¹ = α ^ 2 := by
    have h := congrArg (fun x : ℝ => x⁻¹) hBaseSq
    rw [← inv_pow, hBaseInv] at h
    exact h.symm
  have hTopCoordSummable (i : Fin 2) : Summable (fun j : ℕ =>
      α ^ (2 * j) * energy Q (cubeProjection Q j (fun x => Ftop x i))) := by
    simpa only [hInvSqrt, ← pow_mul] using
      summable_weighted_projections Q hq (hTopCoord i)
  have hRecipCoordSummable (i : Fin 2) : Summable (fun j : ℕ =>
      α ^ (2 * j) * energy Q (cubeProjection Q j (fun x => Frecip x i))) := by
    simpa only [hInvSqrt, ← pow_mul] using
      summable_weighted_projections Q hq (hRecipCoord i)
  have hTopSummable : Summable (fun j : ℕ => α ^ (2 * j) * Etop j) := by
    simp_rw [Etop, Finset.mul_sum]
    exact summable_sum fun i hi => hTopCoordSummable i
  have hRecipSummable : Summable (fun j : ℕ => α ^ (2 * j) * Erecip j) := by
    simp_rw [Erecip, Finset.mul_sum]
    exact summable_sum fun i hi => hRecipCoordSummable i
  have hESummable : Summable (fun j : ℕ => α ^ (2 * j) * E j) := by
    have hpoint : (fun j : ℕ => α ^ (2 * j) * E j) =
        (fun j => α ^ (2 * j) * Etop j + α ^ (2 * j) * Erecip j) := by
      funext j
      simp [E, mul_add]
    rw [hpoint]
    exact hTopSummable.add hRecipSummable
  have hGammaSeries :
      smoothFeedbackCellDirectionalGamma M m Q e ω =
        (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * E j := by
    change vectorWeakHaarEnergy Q Ftop + vectorWeakHaarEnergy Q Frecip = _
    calc
      _ = (1 - α ^ 2) *
          (∑' j : ℕ, α ^ (2 * j) * Etop j +
            ∑' j : ℕ, α ^ (2 * j) * Erecip j) := by
        rw [hTopRep, hRecipRep]
        dsimp [α]
        ring
      _ = (1 - α ^ 2) *
          ∑' j : ℕ, (α ^ (2 * j) * Etop j +
            α ^ (2 * j) * Erecip j) := by
        rw [← hTopSummable.tsum_add hRecipSummable]
      _ = (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * E j := by
        congr 1
        apply tsum_congr
        intro j
        simp [E, mul_add]
  exact ⟨hESummable, hGammaSeries⟩

/-- The trace of the actual directional affine Gram is bounded pathwise by
one copy of the inverse-depth/trace proxy. The basis-summed fixed-depth
estimate supplies the sharp coefficient before the weak-Haar depth sum. -/
theorem smooth_feedback_directional_gamma_trace_le_raw_trace_proxy
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellDirectionalGammaTrace M m Q ω ≤
      Inverse.rawWeakTraceProxy
        (fun j => lemmaVInverseDepthMax Q
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
            (oldCutoffSkewCoefficient m Q ω)) j)
        (fun j => descendantsAverage Q j
          (fun R => traceDefect (openCubeSet R)
            (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
              (oldCutoffSkewCoefficient m Q ω)) 1)) := by
  classical
  let α := Scalar.inverseHistoryDiscount
  let k := oldCutoffSkewCoefficient m Q ω
  let σ := (Annealed.sigmaBar M m : ℝ)
  let a := responseFramePlanarCoefficientField M.nu σ k
  let b : ℕ → ℝ := fun j => lemmaVInverseDepthMax Q a j
  let d : ℕ → ℝ := fun j => descendantsAverage Q j
    (fun R => smoothFeedbackCellT M m R ω)
  let E0 : ℕ → ℝ := fun j =>
    smoothFeedbackCellDirectionalProjectionEnergyAtDepth M m Q (basisVec 0) ω j
  let E1 : ℕ → ℝ := fun j =>
    smoothFeedbackCellDirectionalProjectionEnergyAtDepth M m Q (basisVec 1) ω j
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
      (Annealed.sigmaBar M m).property k
  have hSeries0 := smooth_feedback_directional_gamma_weighted_series
    M m Q (basisVec 0) ω
  have hSeries1 := smooth_feedback_directional_gamma_weighted_series
    M m Q (basisVec 1) ω
  have hE0Summable : Summable (fun j : ℕ => α ^ (2 * j) * E0 j) := by
    simpa [α, E0] using hSeries0.1
  have hE1Summable : Summable (fun j : ℕ => α ^ (2 * j) * E1 j) := by
    simpa [α, E1] using hSeries1.1
  have hESummable : Summable (fun j : ℕ => α ^ (2 * j) * (E0 j + E1 j)) := by
    have hpoint : (fun j : ℕ => α ^ (2 * j) * (E0 j + E1 j)) =
        (fun j => α ^ (2 * j) * E0 j + α ^ (2 * j) * E1 j) := by
      funext j
      ring
    rw [hpoint]
    exact hE0Summable.add hE1Summable
  have hDepth (j : ℕ) : E0 j + E1 j ≤ b j * d j := by
    have h := smooth_feedback_directional_projection_depth_basis_trace_le
      M m Q j ω
    simpa [E0, E1, b, d, a,
      smoothFeedbackCellDirectionalProjectionEnergyAtDepth] using h
  have hAlpha := Scalar.inverse_history_discount_range
  have hAlphaNonneg : 0 ≤ α := hAlpha.1.le
  have hAlphaSqNonneg : 0 ≤ 1 - α ^ 2 := by
    apply sub_nonneg.mpr
    exact (pow_le_one₀ hAlphaNonneg hAlpha.2.le)
  have hTraceNonneg (j : ℕ) : 0 ≤ d j := by
    apply descendantsAverage_nonneg Q j
    intro R hR
    exact smooth_feedback_cell_t_nonneg M m R ω
  have hBNonneg (j : ℕ) : 0 ≤ b j := lemmaVInverseDepthMax_nonneg Q a j
  have hTraceCell (depth : ℕ) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q depth) :
      smoothFeedbackCellT M m R ω =
        traceDefect (openCubeSet R) a 1 := by
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let kR := oldSignedCellCoefficient Q R hRQ k
    let aR := responseFramePlanarCoefficientField M.nu σ kR
    have hCoeff : a =ᵐ[volumeMeasureOn (openCubeSet R)] aR := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      simp only [a, aR, responseFramePlanarCoefficientField]
      rw [old_signed_cell_coefficient_extension_eq Q R hRQ k hx]
    have hCellMatrix : coarseBlockMatrix (openCubeSet R) a =
        smoothFeedbackCellA M m R ω := by
      calc
        coarseBlockMatrix (openCubeSet R) a =
            coarseBlockMatrix (openCubeSet R) aR :=
          coarseBlockMatrix_congr_of_ae_eq hCoeff
        _ = smoothFeedbackCellA M m R ω := by
          let aCube := responseFramePlanarCoefficientField M.nu σ
            (smoothFeedbackCellCubeCoefficient m R ω)
          have hCube : coarseBlockMatrix (cubeSet R) aCube =
              smoothFeedbackCellA M m R ω := by
            have hframe := Variational.response_coarseMatrix_frame_eq
              (measurableSet_cubeSet R) M.nu σ M.nu_pos
              (Annealed.sigmaBar M m).property
              (smoothFeedbackCellCubeCoefficient m R ω)
            rw [hframe, coarseBlockMatrix_congr_of_ae_eq
              (smooth_feedback_cube_physical_coefficient M m R ω)]
            rfl
          calc
            coarseBlockMatrix (openCubeSet R) aR =
                coarseBlockMatrix (openCubeSet R) aCube :=
              coarseBlockMatrix_congr_of_ae_eq
                (smooth_feedback_open_frame_coefficients_ae M m R ω)
            _ = coarseBlockMatrix (cubeSet R) aCube :=
              (Variational.cube_coarseMatrix_eq_open R _).symm
            _ = smoothFeedbackCellA M m R ω := hCube
    rw [ASDExplicitGamma.traceDefect, hCellMatrix]
    simp only [inv_one, one_mul]
    exact smooth_feedback_cell_t_eq_block_traces M m R ω
  have hTraceEq (j : ℕ) : d j = descendantsAverage Q j
      (fun R => traceDefect (openCubeSet R) a 1) := by
    change ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, smoothFeedbackCellT M m R ω =
      ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
        ∑ R ∈ descendantsAtDepth Q j, traceDefect (openCubeSet R) a 1
    congr 1
    apply Finset.sum_congr rfl
    intro R hR
    exact hTraceCell j R hR
  have hTraceSummable : Summable (fun j : ℕ => α ^ j * d j) := by
    have hBase := old_signed_trace_depth_series_summable Q a hEll
    have hEq : (fun j : ℕ => α ^ j * d j) =
        (fun j => α ^ j * descendantsAverage Q j
          (fun R => traceDefect (openCubeSet R) a 1)) := by
      funext j
      rw [hTraceEq j]
    rw [hEq]
    simpa [α] using hBase
  have hDepthMax (j : ℕ) : α ^ j * b j ≤ oldSignedInverseHistory Q a := by
    have h := Inverse.actual_inverse_depth_discount_bound Q a hEll 1
      (by norm_num) j
    simpa [α, b, oldSignedInverseHistory] using h
  have hProxySummable : Summable (fun j : ℕ => α ^ (2 * j) * b j * d j) := by
    apply Summable.of_nonneg_of_le
    · intro j
      exact mul_nonneg
        (mul_nonneg (pow_nonneg hAlphaNonneg _) (hBNonneg j))
        (hTraceNonneg j)
    · intro j
      have hterm : α ^ (2 * j) * b j * d j ≤
          oldSignedInverseHistory Q a * (α ^ j * d j) := by
        calc
          α ^ (2 * j) * b j * d j =
              (α ^ j * b j) * (α ^ j * d j) := by
                rw [show 2 * j = j + j by omega, pow_add]
                ring
          _ ≤ oldSignedInverseHistory Q a * (α ^ j * d j) :=
            mul_le_mul_of_nonneg_right (hDepthMax j)
              (mul_nonneg (pow_nonneg hAlphaNonneg j) (hTraceNonneg j))
      exact hterm
    · exact hTraceSummable.mul_left (oldSignedInverseHistory Q a)
  have hterm (j : ℕ) : α ^ (2 * j) * (E0 j + E1 j) ≤
      α ^ (2 * j) * b j * d j := by
    calc
      α ^ (2 * j) * (E0 j + E1 j) ≤
          α ^ (2 * j) * (b j * d j) :=
        mul_le_mul_of_nonneg_left (hDepth j) (pow_nonneg hAlphaNonneg _)
      _ = α ^ (2 * j) * b j * d j := by ring
  have hRawProxy : Inverse.rawWeakTraceProxy b d =
      Inverse.rawWeakTraceProxy
        (fun j => lemmaVInverseDepthMax Q a j)
        (fun j => descendantsAverage Q j
          (fun R => traceDefect (openCubeSet R) a 1)) := by
    unfold Inverse.rawWeakTraceProxy
    congr 1
    apply tsum_congr
    intro j
    simp only [b]
    rw [hTraceEq j]
  have hGammaSeries : smoothFeedbackCellDirectionalGammaTrace M m Q ω =
      (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * (E0 j + E1 j) := by
    unfold smoothFeedbackCellDirectionalGammaTrace
    rw [Fin.sum_univ_two]
    have h0 : smoothFeedbackCellDirectionalGamma M m Q (basisVec 0) ω =
        (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * E0 j := by
      simpa [α, E0, smoothFeedbackCellDirectionalProjectionEnergyAtDepth] using
        hSeries0.2
    have h1 : smoothFeedbackCellDirectionalGamma M m Q (basisVec 1) ω =
        (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * E1 j := by
      simpa [α, E1, smoothFeedbackCellDirectionalProjectionEnergyAtDepth] using
        hSeries1.2
    calc
      smoothFeedbackCellDirectionalGamma M m Q (basisVec 0) ω +
          smoothFeedbackCellDirectionalGamma M m Q (basisVec 1) ω =
        (1 - α ^ 2) *
          (∑' j : ℕ, α ^ (2 * j) * E0 j +
            ∑' j : ℕ, α ^ (2 * j) * E1 j) := by
              rw [h0, h1]
              ring
      _ = (1 - α ^ 2) * ∑' j : ℕ,
          (α ^ (2 * j) * E0 j + α ^ (2 * j) * E1 j) := by
            rw [← hE0Summable.tsum_add hE1Summable]
      _ = (1 - α ^ 2) *
          ∑' j : ℕ, α ^ (2 * j) * (E0 j + E1 j) := by
            congr 1
            apply tsum_congr
            intro j
            ring
  calc
    smoothFeedbackCellDirectionalGammaTrace M m Q ω =
        (1 - α ^ 2) * ∑' j : ℕ,
          α ^ (2 * j) * (E0 j + E1 j) := hGammaSeries
    _ ≤ (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * b j * d j :=
      mul_le_mul_of_nonneg_left
        (hESummable.tsum_le_tsum hterm hProxySummable) hAlphaSqNonneg
    _ = Inverse.rawWeakTraceProxy b d := by
      unfold Inverse.rawWeakTraceProxy
      rfl
    _ = Inverse.rawWeakTraceProxy
        (fun j => lemmaVInverseDepthMax Q a j)
        (fun j => descendantsAverage Q j
          (fun R => traceDefect (openCubeSet R) a 1)) := hRawProxy

end
end ASDExplicitGamma.Scalar
