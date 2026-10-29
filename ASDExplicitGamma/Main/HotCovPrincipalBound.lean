module

public import ASDExplicitGamma.Main.HotCovAssemble
public import ASDExplicitGamma.Triadic.DiagEstimates
public import ASDExplicitGamma.Triadic.DiagBroken

/-! MA-E-COVARIANCE, step 16: K/P duality for the frozen direction `J z`, the interpolant
contraction `P(∇Iw) ≤ K(∇w)`, and the weak sizes of the cell reciprocal blocks. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian

noncomputable section

/-- Each coordinate of `∇Iw` has convergent positive Haar increments on every tile. -/
theorem hotCov_zfield_positive_series (Q : TriadicCube 2) (d : ℕ)
    (w : H10Function (openCubeSet Q)) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q d)
    (i : Fin 2) :
    Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy U (cubeIncrement U (j + 1) (fun x => hotCovZfield Q d w x i))) := by
  have h := diagInterpolant_gradient_summable Q d 0 w U hU i
  dsimp only at h
  rw [ASDExplicitGamma.Native.old_signed_zero_affine_potential Q w] at h
  exact h

theorem hotCov_Jzfield_positive_series (Q : TriadicCube 2) (d : ℕ)
    (w : H10Function (openCubeSet Q)) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q d) :
    ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy U (cubeIncrement U (j + 1)
        (fun x => planarQuarterTurn (hotCovZfield Q d w x) i))) :=
  positive_series_quarterTurn U (fun x => hotCovZfield Q d w x)
    (fun i => hotCov_zfield_positive_series Q d w U hU i)

/-- K/P duality of the frozen direction with an arbitrary receiver on a tile. -/
theorem hotCov_cross_bound (Q : TriadicCube 2) (d : ℕ) (w : H10Function (openCubeSet Q))
    (U : OldSignedCellIndex Q d) (e : Vec 2 → Vec 2) (he : MemVectorL2 (openCubeSet U.val) e) :
    |hotCovCross U.val (hotCovZfield Q d w) e| ≤
      vectorWeakHaarNorm U.val e *
        vectorPositiveHaarNorm U.val (fun x => planarQuarterTurn (hotCovZfield Q d w x)) := by
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  have hJz := hotCov_memVectorL2_quarterTurn
    ((hotCov_zfield_memL2 Q d w).mono_measure (Measure.restrict_mono_set volume hsub))
  have h := old_signed_vector_average_pairing_bound U.val e
    (fun x => planarQuarterTurn (hotCovZfield Q d w x)) he hJz
    (hotCov_Jzfield_positive_series Q d w U.val U.property)
  have hsym : hotCovCross U.val (hotCovZfield Q d w) e =
      volumeAverage (openCubeSet U.val) (fun x =>
        vecDot (e x) (planarQuarterTurn (hotCovZfield Q d w x))) := by
    unfold hotCovCross
    congr 1
    funext x
    exact vecDot_comm _ _
  rw [hsym]
  exact h

/-- Rotation invariance of the positive energy of the interpolant gradient, and the
contraction `P(∇Iw) ≤ K(∇w)` (tile averages). -/
theorem hotCov_Pz_le_Xk (Q : TriadicCube 2) (d : ℕ) (w : H10Function (openCubeSet Q)) :
    oldSignedCellAverage Q d (fun U => vectorPositiveHaarEnergy U.val
        (fun x => planarQuarterTurn (hotCovZfield Q d w x))) ≤
      lemmaVTiledWeakEnergy Q d w.toH1Function.grad := by
  have h := diagInterpolant_h10_gradient_energy_le Q d w
  have e : oldSignedCellAverage Q d (fun U => vectorPositiveHaarEnergy U.val
      (fun x => planarQuarterTurn (hotCovZfield Q d w x))) =
      lemmaVTiledPositiveEnergy Q d (diagInterpolant Q d w.toH1Function).grad := by
    unfold lemmaVTiledPositiveEnergy
    rw [← old_signed_cell_average_eq_descendantsAverage]
    congr 1
    funext U
    exact main_vectorPositiveHaarEnergy_quarterTurn U.val _
  rw [e]
  exact h

theorem hotCov_canon_neg_ae (Q : TriadicCube 2) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (fun x => (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (-P) : Vec 2 → BlockVec 2) x) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
    fun x => -(oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) x := by
  have h : oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (-P) =
      -oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P := by
    simp only [oldSignedFrameCanonicalField, oldSignedCanonicalAffineField, map_neg]
  exact (Lp.ext_iff.mp h).trans (Lp.coeFn_neg _)

/-- The reciprocal block of the cell comparison is odd in the load. -/
theorem hotCov_cmpRecip_neg_ae (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (P : BlockVec 2) :
    ∀ᵐ x ∂(volumeMeasureOn (openCubeSet U.val)),
      hotCovCmpRecip Q d nu sigma hnu hsigma k U (-P) x =
        -hotCovCmpRecip Q d nu sigma hnu hsigma k U P x := by
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth U.property
  have hS := ae_restrict_of_ae_restrict_of_subset hsub
    (hotCov_canon_neg_ae Q nu sigma hnu hsigma k P)
  have hL := hotCov_canon_neg_ae U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U) P
  filter_upwards [hS, hL] with x hx1 hx2
  unfold hotCovCmpRecip hotCovCmp oldHessianParentCellComparison
  simp only []
  have hneg : ∀ (A : BlockMat 2) (X : BlockVec 2), blockMatVecMul A (-X) = -blockMatVecMul A X := by
    intro A X
    have h := blockMatVecMul_smul A (-1 : ℝ) X
    simpa only [neg_one_smul] using h
  change (blockMatVecMul _ ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (-P) :
        Vec 2 → BlockVec 2) x -
      (oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U) (-P) :
        Vec 2 → BlockVec 2) x)).2 =
    -(blockMatVecMul _ ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P :
        Vec 2 → BlockVec 2) x -
      (oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U) P :
        Vec 2 → BlockVec 2) x)).2
  rw [hx1, hx2]
  have : -(oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) x -
      -(oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U) P :
        Vec 2 → BlockVec 2) x =
      -((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) x -
      (oldSignedFrameCanonicalField U.val nu sigma hnu hsigma (hotCovCellCoef Q d k U) P :
        Vec 2 → BlockVec 2) x) := by abel
  rw [this, hneg]
  rfl

theorem hotCov_cmpRecip_neg_weak (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (P : BlockVec 2) :
    vectorWeakHaarEnergy U.val (hotCovCmpRecip Q d nu sigma hnu hsigma k U (-P)) =
      vectorWeakHaarEnergy U.val (hotCovCmpRecip Q d nu sigma hnu hsigma k U P) := by
  have hm (P' : BlockVec 2) (i : Fin 2) :
      MemLp (fun x => hotCovCmpRecip Q d nu sigma hnu hsigma k U P' x i) 2
        (normalizedCubeMeasure U.val) :=
    memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2
      (hotCov_cmpRecip_memL2 Q d nu sigma hnu hsigma k U P') i)
  have hmneg : ∀ i, MemLp (fun x => (-hotCovCmpRecip Q d nu sigma hnu hsigma k U P x) i) 2
      (normalizedCubeMeasure U.val) := fun i => by
    exact (hm P i).neg
  have hae : (fun x => hotCovCmpRecip Q d nu sigma hnu hsigma k U (-P) x) =ᵐ[
      volume.restrict (cubeSet U.val)]
      (fun x => -hotCovCmpRecip Q d nu sigma hnu hsigma k U P x) := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet U.val]
    exact hotCov_cmpRecip_neg_ae Q d nu sigma hnu hsigma k U P
  rw [main_vector_weak_hair_energy_congr_ae U.val (hm (-P)) hmneg hae]
  exact ASDExplicitGamma.Inverse.vectorWeakHaarEnergy_neg_hot U.val _

/-- The pairing involution of the four canonical loads. -/
def hotCovSigma : BlockCoord 2 ≃ BlockCoord 2 :=
  (Equiv.sumComm (Fin 2) (Fin 2)).trans (Equiv.sumCongr Fin.revPerm Fin.revPerm)

theorem hotCov_pairLoad_weak (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (U : OldSignedCellIndex Q d) (c : BlockCoord 2) :
    vectorWeakHaarEnergy U.val (hotCovCmpRecip Q d nu sigma hnu hsigma k U
        (hotCovPairLoadC c (hotCovJcol (hotCovIdxC c)))) =
      vectorWeakHaarEnergy U.val (hotCovCmpRecip Q d nu sigma hnu hsigma k U
        (blockBasis (hotCovSigma c))) := by
  have e1 : hotCovPairLoadC (Sum.inl 0) (hotCovJcol (hotCovIdxC (Sum.inl 0))) =
      blockBasis (hotCovSigma (Sum.inl 0)) := by
    ext a <;> fin_cases a <;> simp [hotCovPairLoadC, hotCovJcol, hotCovIdxC, hotCovSigma,
      blockBasis, basisVec, responsePlanarJ, Pi.single_apply]
  have e2 : hotCovPairLoadC (Sum.inl 1) (hotCovJcol (hotCovIdxC (Sum.inl 1))) =
      -blockBasis (hotCovSigma (Sum.inl 1)) := by
    ext a <;> fin_cases a <;> simp [hotCovPairLoadC, hotCovJcol, hotCovIdxC, hotCovSigma,
      blockBasis, basisVec, responsePlanarJ, Pi.single_apply]
  have e3 : hotCovPairLoadC (Sum.inr 0) (hotCovJcol (hotCovIdxC (Sum.inr 0))) =
      blockBasis (hotCovSigma (Sum.inr 0)) := by
    ext a <;> fin_cases a <;> simp [hotCovPairLoadC, hotCovJcol, hotCovIdxC, hotCovSigma,
      blockBasis, basisVec, responsePlanarJ, Pi.single_apply]
  have e4 : hotCovPairLoadC (Sum.inr 1) (hotCovJcol (hotCovIdxC (Sum.inr 1))) =
      -blockBasis (hotCovSigma (Sum.inr 1)) := by
    ext a <;> fin_cases a <;> simp [hotCovPairLoadC, hotCovJcol, hotCovIdxC, hotCovSigma,
      blockBasis, basisVec, responsePlanarJ, Pi.single_apply]
  have f1 := congrArg (fun P => vectorWeakHaarEnergy U.val
    (hotCovCmpRecip Q d nu sigma hnu hsigma k U P)) e1
  have f2 := congrArg (fun P => vectorWeakHaarEnergy U.val
    (hotCovCmpRecip Q d nu sigma hnu hsigma k U P)) e2
  have f3 := congrArg (fun P => vectorWeakHaarEnergy U.val
    (hotCovCmpRecip Q d nu sigma hnu hsigma k U P)) e3
  have f4 := congrArg (fun P => vectorWeakHaarEnergy U.val
    (hotCovCmpRecip Q d nu sigma hnu hsigma k U P)) e4
  simp only [hotCov_cmpRecip_neg_weak] at f2 f4
  rcases c with i | i
  · fin_cases i
    · exact f1
    · exact f2
  · fin_cases i
    · exact f3
    · exact f4

/-- The principal pairing is the cross of `J z` with the reciprocal blocks of the drop. -/
theorem hotCov_prin_eq (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    hotCovPrinTotal Q d nu sigma hnu hsigma k =
      ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
        hotCovCross U.val
          (hotCovZfield Q d (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)))
          (hotCovCmpRecip Q d nu sigma hnu hsigma k U
            (hotCovPairLoadC c (hotCovJcol (hotCovIdxC c))))) := by
  unfold hotCovPrinTotal
  rw [old_signed_cell_average_sum Q d Finset.univ]
  apply Finset.sum_congr rfl
  intro c _
  rcases c with i | i
  · exact hotCov_top_principal_identity Q d nu sigma hnu hsigma k _ (hotCovJcol i)
  · exact hotCov_bot_principal_identity Q d nu sigma hnu hsigma k _ (hotCovJcol i)

/-- The principal term is bounded by the geometric mean of the positive size of `∇Iw`
and the weak size of the drop's reciprocal blocks. -/
theorem hotCov_prin_bound (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    |hotCovPrinTotal Q d nu sigma hnu hsigma k| ≤
      Real.sqrt (∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
        vectorPositiveHaarEnergy U.val (fun x => planarQuarterTurn
          (hotCovZfield Q d (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)) x)))) *
      Real.sqrt (∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
        vectorWeakHaarEnergy U.val
          (hotCovCmpRecip Q d nu sigma hnu hsigma k U (blockBasis c)))) := by
  classical
  let a : OldSignedCellIndex Q d → BlockCoord 2 → ℝ := fun U c => vectorPositiveHaarNorm U.val
    (fun x => planarQuarterTurn
      (hotCovZfield Q d (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)) x))
  let β : OldSignedCellIndex Q d → BlockCoord 2 → ℝ := fun U c => vectorWeakHaarNorm U.val
    (hotCovCmpRecip Q d nu sigma hnu hsigma k U
      (hotCovPairLoadC c (hotCovJcol (hotCovIdxC c))))
  let G : OldSignedCellIndex Q d → BlockCoord 2 → ℝ := fun U c => hotCovCross U.val
    (hotCovZfield Q d (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)))
    (hotCovCmpRecip Q d nu sigma hnu hsigma k U
      (hotCovPairLoadC c (hotCovJcol (hotCovIdxC c))))
  have hG : ∀ U c, |G U c| ≤ β U c * a U c := fun U c =>
    hotCov_cross_bound Q d _ U _ (hotCov_cmpRecip_memL2 Q d nu sigma hnu hsigma k U _)
  have hprin : hotCovPrinTotal Q d nu sigma hnu hsigma k =
      oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2, G U c) := by
    rw [hotCov_prin_eq, old_signed_cell_average_sum Q d Finset.univ]
  have h1 : |oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2, G U c)| ≤
      oldSignedCellAverage Q d (fun U => Real.sqrt (∑ c, a U c ^ 2) * Real.sqrt (∑ c, β U c ^ 2)) := by
    refine (old_signed_cell_average_abs_le Q d _).trans (old_signed_cell_average_mono Q d (fun U => ?_))
    calc |∑ c, G U c| ≤ ∑ c, |G U c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, a U c * β U c := Finset.sum_le_sum (fun c _ => by rw [mul_comm]; exact hG U c)
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have h2 := old_signed_cell_average_cauchy Q d (fun U => Real.sqrt (∑ c, a U c ^ 2))
    (fun U => Real.sqrt (∑ c, β U c ^ 2))
  have hsa : ∀ U : OldSignedCellIndex Q d, Real.sqrt (∑ c, a U c ^ 2) ^ 2 = ∑ c, a U c ^ 2 :=
    fun U => Real.sq_sqrt (Finset.sum_nonneg (fun c _ => sq_nonneg _))
  have hsb : ∀ U : OldSignedCellIndex Q d, Real.sqrt (∑ c, β U c ^ 2) ^ 2 = ∑ c, β U c ^ 2 :=
    fun U => Real.sq_sqrt (Finset.sum_nonneg (fun c _ => sq_nonneg _))
  simp only [hsa, hsb] at h2
  have hA : oldSignedCellAverage Q d (fun U => ∑ c, a U c ^ 2) =
      ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
        vectorPositiveHaarEnergy U.val (fun x => planarQuarterTurn
          (hotCovZfield Q d (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)) x))) := by
    rw [old_signed_cell_average_sum Q d Finset.univ]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    funext U
    simp only [a, vectorPositiveHaarNorm, Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg _ _)]
  have hB : oldSignedCellAverage Q d (fun U => ∑ c, β U c ^ 2) =
      ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
        vectorWeakHaarEnergy U.val
          (hotCovCmpRecip Q d nu sigma hnu hsigma k U (blockBasis c))) := by
    rw [old_signed_cell_average_sum Q d Finset.univ]
    rw [← Equiv.sum_comp hotCovSigma (fun c => oldSignedCellAverage Q d (fun U =>
        vectorWeakHaarEnergy U.val
          (hotCovCmpRecip Q d nu sigma hnu hsigma k U (blockBasis c))))]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    funext U
    simp only [β, vectorWeakHaarNorm, Real.sq_sqrt (vectorWeakHaarEnergy_nonneg _ _)]
    exact hotCov_pairLoad_weak Q d nu sigma hnu hsigma k U c
  rw [hA, hB] at h2
  rw [hprin]
  exact h1.trans h2

/-- Double Cauchy over loads and tiles. -/
theorem hotCov_total_cauchy (Q : TriadicCube 2) (d : ℕ)
    (a β G : OldSignedCellIndex Q d → BlockCoord 2 → ℝ)
    (hG : ∀ U c, |G U c| ≤ β U c * a U c) :
    |oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2, G U c)| ≤
      Real.sqrt (oldSignedCellAverage Q d (fun U => ∑ c, a U c ^ 2)) *
        Real.sqrt (oldSignedCellAverage Q d (fun U => ∑ c, β U c ^ 2)) := by
  have h1 : |oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2, G U c)| ≤
      oldSignedCellAverage Q d (fun U => Real.sqrt (∑ c, a U c ^ 2) * Real.sqrt (∑ c, β U c ^ 2)) := by
    refine (old_signed_cell_average_abs_le Q d _).trans (old_signed_cell_average_mono Q d (fun U => ?_))
    calc |∑ c, G U c| ≤ ∑ c, |G U c| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ c, a U c * β U c := Finset.sum_le_sum (fun c _ => by rw [mul_comm]; exact hG U c)
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have h2 := old_signed_cell_average_cauchy Q d (fun U => Real.sqrt (∑ c, a U c ^ 2))
    (fun U => Real.sqrt (∑ c, β U c ^ 2))
  have hsa : ∀ U : OldSignedCellIndex Q d, Real.sqrt (∑ c, a U c ^ 2) ^ 2 = ∑ c, a U c ^ 2 :=
    fun U => Real.sq_sqrt (Finset.sum_nonneg (fun c _ => sq_nonneg _))
  have hsb : ∀ U : OldSignedCellIndex Q d, Real.sqrt (∑ c, β U c ^ 2) ^ 2 = ∑ c, β U c ^ 2 :=
    fun U => Real.sq_sqrt (Finset.sum_nonneg (fun c _ => sq_nonneg _))
  simp only [hsa, hsb] at h2
  exact h1.trans h2

/-- The weak size of the covariance-error receivers, over loads and tiles. -/
def hotCovKE2 (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2, vectorWeakHaarEnergy U.val
    (hotCovRcvC Q d nu sigma hnu hsigma k c U
      (hotCovErrCol Q U.val b L (hotCovPlusC c) (hotCovIdxC c))))

theorem hotCov_err_bound (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    |hotCovErrTotal Q d nu sigma hnu hsigma k b L| ≤
      Real.sqrt (∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
        vectorPositiveHaarEnergy U.val (fun x => planarQuarterTurn
          (hotCovZfield Q d (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)) x)))) *
      Real.sqrt (hotCovKE2 Q d nu sigma hnu hsigma k b L) := by
  classical
  have h := hotCov_total_cauchy Q d
    (fun U c => vectorPositiveHaarNorm U.val (fun x => planarQuarterTurn
      (hotCovZfield Q d (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)) x)))
    (fun U c => vectorWeakHaarNorm U.val (hotCovRcvC Q d nu sigma hnu hsigma k c U
      (hotCovErrCol Q U.val b L (hotCovPlusC c) (hotCovIdxC c))))
    (fun U c => hotCovEll Q d U
      (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c))
      (hotCovRcvC Q d nu sigma hnu hsigma k c U
        (hotCovErrCol Q U.val b L (hotCovPlusC c) (hotCovIdxC c))))
    (fun U c => hotCov_cross_bound Q d _ U _ (hotCovRcvC_memL2 Q d nu sigma hnu hsigma k c U _))
  have hA : oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2, vectorPositiveHaarNorm U.val
      (fun x => planarQuarterTurn (hotCovZfield Q d
        (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)) x)) ^ 2) =
      ∑ c : BlockCoord 2, oldSignedCellAverage Q d (fun U =>
        vectorPositiveHaarEnergy U.val (fun x => planarQuarterTurn
          (hotCovZfield Q d (hotPatchPotential Q d nu sigma hnu hsigma k (blockBasis c)) x))) := by
    rw [old_signed_cell_average_sum Q d Finset.univ]
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    funext U
    simp only [vectorPositiveHaarNorm, Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg _ _)]
  have hB : oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2, vectorWeakHaarNorm U.val
      (hotCovRcvC Q d nu sigma hnu hsigma k c U
        (hotCovErrCol Q U.val b L (hotCovPlusC c) (hotCovIdxC c))) ^ 2) =
      hotCovKE2 Q d nu sigma hnu hsigma k b L := by
    unfold hotCovKE2
    congr 1
    funext U
    apply Finset.sum_congr rfl
    intro c _
    simp only [vectorWeakHaarNorm, Real.sq_sqrt (vectorWeakHaarEnergy_nonneg _ _)]
  rw [hA, hB] at h
  exact h

/-- The weak size of the actual affine receivers, over modes, loads and tiles. -/
def hotCovKaff2 (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l}) : ℝ :=
  oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2,
    ∑' n : whiteBasisIndex, vectorWeakHaarEnergy U.val
      (hotCovRcvC Q d nu sigma hnu hsigma k c U
        (hotCovFlatMeanVec Q b L (hotCovPlusC c) U.val n (hotCovIdxC c))))

theorem hotCov_res_bound (Q : TriadicCube 2) (d : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (hL : ∀ R ∈ descendantsAtDepth Q d, cubeScaleFactor R * 3 ^ 6 ≤ L.1)
    (hmesh : diagMeshRadius Q d * 3 ^ 6 ≤ L.1) :
    |hotCovResTotal Q d nu sigma hnu hsigma k b L| ≤
      Real.sqrt (∑' n : whiteBasisIndex, ∑ c : BlockCoord 2,
        descendantsAverage Q d (fun U => vectorPositiveHaarEnergy U
          (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U x))) *
      Real.sqrt (hotCovKaff2 Q d nu sigma hnu hsigma k b L) := by
  classical
  let A : OldSignedCellIndex Q d → BlockCoord 2 → ℝ := fun U c =>
    ∑' n : whiteBasisIndex, vectorPositiveHaarEnergy U.val
      (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U.val x)
  let B : OldSignedCellIndex Q d → BlockCoord 2 → ℝ := fun U c =>
    ∑' n : whiteBasisIndex, vectorWeakHaarEnergy U.val
      (hotCovRcvC Q d nu sigma hnu hsigma k c U
        (hotCovFlatMeanVec Q b L (hotCovPlusC c) U.val n (hotCovIdxC c)))
  have hA0 : ∀ U c, 0 ≤ A U c := fun U c =>
    tsum_nonneg (fun n => vectorPositiveHaarEnergy_nonneg _ _)
  have hB0 : ∀ U c, 0 ≤ B U c := fun U c =>
    tsum_nonneg (fun n => vectorWeakHaarEnergy_nonneg _ _)
  have h := hotCov_total_cauchy Q d (fun U c => Real.sqrt (A U c)) (fun U c => Real.sqrt (B U c))
    (fun U c => hotCovResSeries Q d nu sigma hnu hsigma k b L U (blockBasis c) (hotCovPlusC c)
      (hotCovIdxC c) (hotCovRcvC Q d nu sigma hnu hsigma k c U))
    (fun U c => ((hotCov_cell_series_C Q d nu sigma hnu hsigma k b L hL hmesh U c).1).trans
      (le_of_eq (mul_comm _ _)))
  simp only [Real.sq_sqrt (hA0 _ _), Real.sq_sqrt (hB0 _ _)] at h
  have hApart : oldSignedCellAverage Q d (fun U => ∑ c, A U c) =
      ∑' n : whiteBasisIndex, ∑ c : BlockCoord 2,
        descendantsAverage Q d (fun U => vectorPositiveHaarEnergy U
          (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U x)) := by
    have hs : ∀ (U : OldSignedCellIndex Q d) (c : BlockCoord 2), Summable (fun n : whiteBasisIndex =>
        vectorPositiveHaarEnergy U.val
          (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U.val x)) :=
      fun U c => hotCov_rem_sq_summable Q d nu sigma hnu hsigma k b L hL hmesh U.val U.property c
    have e1 : ∀ U : OldSignedCellIndex Q d, ∑ c, A U c =
        ∑' n : whiteBasisIndex, ∑ c : BlockCoord 2, vectorPositiveHaarEnergy U.val
          (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U.val x) := by
      intro U
      exact (Summable.tsum_finsetSum (fun c _ => hs U c)).symm
    have hsum : ∀ U : OldSignedCellIndex Q d, Summable (fun n : whiteBasisIndex =>
        ∑ c : BlockCoord 2, vectorPositiveHaarEnergy U.val
          (fun x => hotCovRem Q d nu sigma hnu hsigma k b L n (blockBasis c) U.val x)) :=
      fun U => summable_sum (fun c _ => hs U c)
    simp_rw [e1]
    rw [← (old_signed_cell_average_series Q d _ hsum).2]
    apply tsum_congr
    intro n
    rw [old_signed_cell_average_sum Q d Finset.univ]
    apply Finset.sum_congr rfl
    intro c _
    rw [← old_signed_cell_average_eq_descendantsAverage]
  have hres : hotCovResTotal Q d nu sigma hnu hsigma k b L =
      oldSignedCellAverage Q d (fun U => ∑ c : BlockCoord 2,
        hotCovResSeries Q d nu sigma hnu hsigma k b L U (blockBasis c) (hotCovPlusC c)
          (hotCovIdxC c) (hotCovRcvC Q d nu sigma hnu hsigma k c U)) := rfl
  rw [hApart] at h
  rw [hres]
  exact h

end

end ASDExplicitGamma.Main
