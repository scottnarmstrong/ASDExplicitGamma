module

public import ASDExplicitGamma.Variational.ForcedSource
public import ASDExplicitGamma.Triadic.HaarNormTriangle
public import ASDExplicitGamma.Triadic.PositiveNormAggregation

/-! The corrected all-descendant feedback estimate for the actual pure source. -/

@[expose] public section
namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Triadic
open scoped BigOperators

noncomputable section

private theorem forcedSource_inverseHistory_descendant_le (Q R : TriadicCube 2)
    (j : ℕ) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hR : R ∈ descendantsAtDepth Q j) :
    lemmaVInverseHistory R a ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
      ((3 : ℝ) ^ (1 / 4 : ℝ)) ^ j *
        lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
  let q : ℝ := (3 : ℝ) ^ (1 / 4 : ℝ)
  let r : ℝ := q⁻¹
  let M : ℕ → ℝ := lemmaVInverseDepthMax R a
  let N : ℕ → ℝ := lemmaVInverseDepthMax Q a
  have hq : 1 < q := by
    dsimp [q]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hq)).2 hq
  have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)
  have hsM : Summable (fun k : ℕ => r ^ k * M k) := by
    simpa [M, r, q] using lemmaVInverseHistory_summable R hEllR hq
  have hsN : Summable (fun k : ℕ => r ^ k * N k) := by
    simpa [N, r, q] using lemmaVInverseHistory_summable Q hEll hq
  have hMle (k : ℕ) : M k ≤ N (j + k) := by
    change lemmaVInverseDepthMax R a k ≤ lemmaVInverseDepthMax Q a (j + k)
    unfold lemmaVInverseDepthMax
    apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty R k)
    intro S hS
    unfold Book.Ch02.finsetSupReal
    exact le_csSup (((Set.toFinite _).image _).bddAbove)
      ⟨S, mem_descendantsAtDepth_add hR hS, rfl⟩
  have htailSummable : Summable (fun k : ℕ => r ^ (j + k) * N (j + k)) := by
    simpa [N, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (summable_nat_add_iff j).2 hsN
  have hshiftSummable : Summable (fun k : ℕ => r ^ k * N (j + k)) := by
    have hmul := htailSummable.mul_left (r⁻¹ ^ j)
    have heq : (fun k : ℕ => r ^ k * N (j + k)) =
        (fun k => r⁻¹ ^ j * (r ^ (j + k) * N (j + k))) := by
      funext k
      have hcancel : r⁻¹ ^ j * r ^ j = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
      rw [pow_add]
      calc
        r ^ k * N (j + k) = 1 * (r ^ k * N (j + k)) := by ring
        _ = (r⁻¹ ^ j * r ^ j) * (r ^ k * N (j + k)) := by rw [hcancel]
        _ = r⁻¹ ^ j * (r ^ j * r ^ k * N (j + k)) := by ring
    rw [heq]
    exact hmul
  have hterm (k : ℕ) : r ^ k * M k ≤ r ^ k * N (j + k) :=
    mul_le_mul_of_nonneg_left (hMle k) (pow_nonneg hr.le k)
  have hle := hsM.tsum_le_tsum hterm hshiftSummable
  have htailBound :
      (∑' k : ℕ, r ^ (j + k) * N (j + k)) ≤ ∑' k : ℕ, r ^ k * N k := by
    have hsplit := hsN.sum_add_tsum_nat_add j
    have hprefix : 0 ≤ ∑ k ∈ Finset.range j, r ^ k * N k :=
      Finset.sum_nonneg fun k hk => mul_nonneg (pow_nonneg hr.le _)
        (lemmaVInverseDepthMax_nonneg Q a k)
    have hsplit' : (∑ k ∈ Finset.range j, r ^ k * N k) +
        (∑' k : ℕ, r ^ (j + k) * N (j + k)) = ∑' k : ℕ, r ^ k * N k := by
      simpa [N, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsplit
    linarith
  have hhistory :
      lemmaVInverseHistory R a q = (1 - r) * ∑' k : ℕ, r ^ k * M k := rfl
  have hhistoryQ :
      lemmaVInverseHistory Q a q = (1 - r) * ∑' k : ℕ, r ^ k * N k := rfl
  have hShiftEq : (∑' k : ℕ, r ^ k * N (j + k)) =
      r⁻¹ ^ j * (∑' k : ℕ, r ^ (j + k) * N (j + k)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    have hcancel : r⁻¹ ^ j * r ^ j = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
    calc
      r ^ k * N (j + k) = 1 * (r ^ k * N (j + k)) := by ring
      _ = (r⁻¹ ^ j * r ^ j) * (r ^ k * N (j + k)) := by rw [hcancel]
      _ = r⁻¹ ^ j * (r ^ (j + k) * N (j + k)) := by rw [pow_add]; ring
  have hsumBound : (∑' k : ℕ, r ^ k * M k) ≤
      r⁻¹ ^ j * (∑' k : ℕ, r ^ (j + k) * N (j + k)) := by
    exact hle.trans_eq hShiftEq
  have hfactor : 0 ≤ 1 - r := by linarith
  rw [hhistory, hhistoryQ]
  calc
    (1 - r) * (∑' k : ℕ, r ^ k * M k) ≤
        (1 - r) * (r⁻¹ ^ j * ∑' k : ℕ, r ^ (j + k) * N (j + k)) :=
      mul_le_mul_of_nonneg_left hsumBound hfactor
    _ = r⁻¹ ^ j * ((1 - r) * ∑' k : ℕ, r ^ (j + k) * N (j + k)) := by ring
    _ ≤ r⁻¹ ^ j * ((1 - r) * ∑' k : ℕ, r ^ k * N k) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htailBound hfactor)
        (pow_nonneg (inv_nonneg.mpr hr.le) j)
    _ = q ^ j * ((1 - r) * ∑' k : ℕ, r ^ k * N k) := by
      have hfac : r⁻¹ ^ j = q ^ j := by simp [r, q]
      rw [hfac]

theorem forcedSource_local_paired_euclidean
    {Q : TriadicCube 2} {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (W : BlockState 2) (hWpot : IsBlockPotentialOn (openCubeSet Q) W)
    (hWsol : IsBlockSolenoidalOn (openCubeSet Q) W)
    (hWmem : MemBlockL2 (openCubeSet Q) W.eval)
    (hWlower : MemVectorL2 (openCubeSet Q)
      (fun x => (blockMatVecMul (blockCoeffField a x) (W.eval x)).2))
    {F : Vec 2 → Vec 2} (hF : MemVectorL2 (openCubeSet Q) F)
    (hforced : ∀ T : BlockState 2, ScalarVariation (openCubeSet Q) T.eval →
      volumeAverage (openCubeSet Q) (blockPairingIntegrand a T W) =
        volumeAverage (openCubeSet Q) (fun x => vecDot (T.potential x) (F x))) :
    vecNormSq (pairedPotentialMean (openCubeSet Q) W) +
      vecNormSq (pairedFluxImageMean (openCubeSet Q) a W +
        pairedBesselSourceCorrectionVector hEll F) ≤
      Book.Ch02.matrixNorm (coarseBlockMatrix (openCubeSet Q) a).lowerRight *
        blockPairingAverage (openCubeSet Q) a W W := by
  let U := openCubeSet Q
  let D : Mat 2 := (coarseBlockMatrix U a).lowerRight
  let p := pairedPotentialMean U W
  let q := pairedFluxImageMean U a W + pairedBesselSourceCorrectionVector hEll F
  let forcedSourceLocalFiniteMeasure : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hvol : 0 < (MeasureTheory.volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  obtain ⟨_, hCoarse, _, _, _, _, hDpos, _⟩ :=
    exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet Q) hEll hvol
  have hD : D.PosDef := by
    change (coarseBlockMatrix U a).lowerRight.PosDef
    rw [coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarse]
    exact hDpos
  have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit
  have hDleft : ∀ ξ : Vec 2, matVecMul D (matVecMul D⁻¹ ξ) = ξ := by
    intro ξ
    rw [matVecMul_mul, Matrix.mul_nonsing_inv D hDdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hBessel := pairedBessel_forced_openCubeSet hEll W hWpot hWsol hWmem
    hWlower hF hforced
  have hmetricP := Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    hD.posSemidef hDleft p
  have hmetricQ := Book.Ch02.vecNormSq_le_matrixNorm_mul_vecDot_matVecMul_of_posSemidef_of_leftInverse
    hD.posSemidef hDleft q
  have hnorm : vecNormSq p + vecNormSq q ≤ Book.Ch02.matrixNorm D *
      (vecDot p (matVecMul D⁻¹ p) + vecDot q (matVecMul D⁻¹ q)) := by
    calc
      _ ≤ Book.Ch02.matrixNorm D * vecDot p (matVecMul D⁻¹ p) +
          Book.Ch02.matrixNorm D * vecDot q (matVecMul D⁻¹ q) := add_le_add hmetricP hmetricQ
      _ = _ := by ring
  have hb : 0 ≤ Book.Ch02.matrixNorm D := Book.Ch02.matrixNorm_nonneg D
  calc
    vecNormSq (pairedPotentialMean U W) + vecNormSq
        (pairedFluxImageMean U a W + pairedBesselSourceCorrectionVector hEll F) =
      vecNormSq p + vecNormSq q := by rfl
    _ ≤ Book.Ch02.matrixNorm D *
        (vecDot p (matVecMul D⁻¹ p) + vecDot q (matVecMul D⁻¹ q)) := hnorm
    _ ≤ Book.Ch02.matrixNorm D * blockPairingAverage U a W W :=
      mul_le_mul_of_nonneg_left hBessel hb

noncomputable def forcedSource_meanLevel (Q : TriadicCube 2) (j : ℕ)
    (F : Vec 2 → Vec 2) : ℝ :=
  descendantsAverage Q j (fun R => vecNormSq
    (fun i => cubeAverage R (fun x => F x i)))

private theorem forcedSource_projectionEnergy_eq_meanLevel (Q : TriadicCube 2)
    (j : ℕ) {F : Vec 2 → Vec 2}
    (hF : ∀ i : Fin 2, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    (∑ i : Fin 2, energy Q (cubeProjection Q j (fun x => F x i))) =
      forcedSource_meanLevel Q j F := by
  simp_rw [← pairing_projection_energy Q j (hF _),
    pairing_projection_right Q j _ (hF _)]
  simp only [forcedSource_meanLevel, descendantsAverage, vecNormSq, vecDot]
  rw [← Finset.mul_sum, Finset.sum_comm]

theorem forcedSource_meanLevel_series_summable (Q : TriadicCube 2)
    {F : Vec 2 → Vec 2}
    (hF : ∀ i : Fin 2, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    Summable (fun j : ℕ => (Real.sqrt 3)⁻¹ ^ j * forcedSource_meanLevel Q j F) := by
  let q : ℝ := Real.sqrt 3
  let w : ℝ := q⁻¹
  have hq : 1 < q := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hsCoord (i : Fin 2) : Summable (fun j : ℕ => w ^ j *
      energy Q (cubeProjection Q j (fun x => F x i))) := by
    simpa [w, q] using summable_weighted_projections Q hq (hF i)
  have hsAll : Summable (fun j : ℕ => w ^ j *
      (∑ i : Fin 2, energy Q (cubeProjection Q j (fun x => F x i)))) := by
    simpa only [Finset.mul_sum] using summable_sum fun i _ => hsCoord i
  have heq : (fun j : ℕ => w ^ j * forcedSource_meanLevel Q j F) =
      (fun j => w ^ j *
        (∑ i : Fin 2, energy Q (cubeProjection Q j (fun x => F x i)))) := by
    funext j
    rw [forcedSource_projectionEnergy_eq_meanLevel Q j hF]
  rw [heq]
  simpa [w, q] using hsAll

theorem forcedSource_volumeAverage_congr_ae {U : Set (Vec 2)}
    {f g : Vec 2 → ℝ}
    (hfg : f =ᵐ[volumeMeasureOn U] g) :
    volumeAverage U f = volumeAverage U g := by
  unfold volumeAverage
  congr 1
  exact integral_congr_ae hfg

theorem forcedSource_volumeAverageVec_congr_ae {U : Set (Vec 2)}
    {f g : Vec 2 → Vec 2}
    (hfg : f =ᵐ[volumeMeasureOn U] g) :
    volumeAverageVec U f = volumeAverageVec U g := by
  funext i
  apply forcedSource_volumeAverage_congr_ae
  exact hfg.mono fun x hx => congrArg (fun z : Vec 2 => z i) hx

theorem forcedSource_volumeAverage_eq_cubeAverage (R : TriadicCube 2)
    (f : Vec 2 → ℝ) :
    volumeAverage (openCubeSet R) f = cubeAverage R f := by
  rw [cubeAverage_eq_integralAverage_openCubeSet]
  rfl

private theorem forcedSource_sqrt_vecNormSq_add_le (x y : Vec 2) :
    Real.sqrt (vecNormSq (x + y)) ≤
      Real.sqrt (vecNormSq x) + Real.sqrt (vecNormSq y) := by
  unfold vecNormSq vecDot
  simpa [vecNormSq, vecDot, pow_two] using sqrt_finset_sq_add_le Finset.univ x y

theorem forcedSource_sqrt_vecNormSq_sub_le (x y : Vec 2) :
    Real.sqrt (vecNormSq x) ≤
      Real.sqrt (vecNormSq (x + y)) + Real.sqrt (vecNormSq y) := by
  have h := forcedSource_sqrt_vecNormSq_add_le (x + y) (-y)
  simpa [vecNormSq, vecDot, pow_two] using h

theorem forcedSource_weakEnergy_eq_meanSeries (Q : TriadicCube 2)
    {F : Vec 2 → Vec 2}
    (hF : ∀ i : Fin 2, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q)) :
    vectorWeakHaarEnergy Q F =
      (1 - (Real.sqrt 3)⁻¹) * ∑' j : ℕ,
        (Real.sqrt 3)⁻¹ ^ j * forcedSource_meanLevel Q j F := by
  let q : ℝ := Real.sqrt 3
  let w : ℝ := q⁻¹
  have hq : 1 < q := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hsCoord (i : Fin 2) : Summable (fun j : ℕ => w ^ j *
      energy Q (cubeProjection Q j (fun x => F x i))) := by
    simpa [w, q] using summable_weighted_projections Q hq (hF i)
  have hsAll : Summable (fun j : ℕ => w ^ j *
      (∑ i : Fin 2, energy Q (cubeProjection Q j (fun x => F x i)))) := by
    simpa only [Finset.mul_sum] using summable_sum fun i _ => hsCoord i
  unfold vectorWeakHaarEnergy
  calc
    (∑ i : Fin 2, dualEnergy Q q (fun x => F x i)) =
        ∑ i : Fin 2, (1 - w) * ∑' j : ℕ, w ^ j *
          energy Q (cubeProjection Q j (fun x => F x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa [q, w] using dualEnergy_eq Q hq (hF i)
    _ = (1 - w) * ∑' j : ℕ, w ^ j *
          (∑ i : Fin 2, energy Q (cubeProjection Q j (fun x => F x i))) := by
      rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun i _ => hsCoord i)]
      congr 1
      exact tsum_congr fun j => (Finset.mul_sum _ _ _).symm
    _ = (1 - w) * ∑' j : ℕ, w ^ j * forcedSource_meanLevel Q j F := by
      apply congrArg (fun s : ℝ => (1 - w) * s)
      apply tsum_congr
      intro j
      exact congrArg (fun e : ℝ => w ^ j * e)
        (forcedSource_projectionEnergy_eq_meanLevel Q j hF)
    _ = _ := by rfl

noncomputable def forcedSource_feedback_shift (Q : TriadicCube 2)
    (j : ℕ) (R : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (F : Vec 2 → Vec 2) : Vec 2 :=
  if hR : R ∈ descendantsAtDepth Q j then
    pairedBesselSourceCorrectionVector
      (hEll.mono (measurableSet_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR)) F
  else 0

noncomputable def forcedSource_feedback_shiftLevel (Q : TriadicCube 2)
    (j : ℕ) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (F : Vec 2 → Vec 2) : ℝ :=
  descendantsAverage Q j (fun R => vecNormSq
    (forcedSource_feedback_shift Q j R hEll F))

theorem forcedSource_feedback_shift_weakEnergy_le (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {F : Vec 2 → Vec 2} (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hFpos : ∀ i : Fin 2, Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) (fun x => F x i)))) :
    Summable (fun j : ℕ => (Real.sqrt 3)⁻¹ ^ j *
      forcedSource_feedback_shiftLevel Q j hEll F) ∧
      (1 - (Real.sqrt 3)⁻¹) * (∑' j : ℕ, (Real.sqrt 3)⁻¹ ^ j *
        forcedSource_feedback_shiftLevel Q j hEll F) ≤
        (Real.sqrt 3)⁻¹ *
          (lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ))) ^ 2 *
            forcedSourceCircleEnergy Q F := by
  let q : ℝ := (3 : ℝ) ^ (1 / 4 : ℝ)
  let w : ℝ := (Real.sqrt 3)⁻¹
  let H : ℝ := lemmaVInverseHistory Q a q
  have hq : 1 < q := by
    dsimp [q]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hwpos : 0 < w := by dsimp [w]; positivity
  have hwle : w < 1 := by
    have hroot : 1 < Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
    dsimp [w]
    exact (inv_lt_one₀ (by positivity)).2 hroot
  have hw0 : 0 ≤ w := hwpos.le
  have hwfactor : 0 ≤ 1 - w := by linarith
  have hHnonneg : 0 ≤ H := by
    dsimp [H, q]
    exact lemmaVInverseHistory_nonneg Q a
      (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hCircleNonneg : 0 ≤ forcedSourceCircleEnergy Q F :=
    forcedSourceCircleEnergy_nonneg Q F
  have hq2 : q ^ 2 = Real.sqrt 3 := by
    dsimp [q]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3)
      (1 / 4 : ℝ) 2]
    norm_num [Real.sqrt_eq_rpow]
  have hq2w : q ^ 2 * w = 1 := by
    rw [hq2]
    dsimp [w]
    exact mul_inv_cancel₀ (by positivity)
  let L : ℕ → ℝ := fun j => forcedSource_feedback_shiftLevel Q j hEll F
  have hLnonneg (j : ℕ) : 0 ≤ L j := by
    unfold L forcedSource_feedback_shiftLevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  have hLbound (j : ℕ) : L j ≤ w * H ^ 2 * forcedSourceCircleEnergy Q F := by
    let D := descendantsAtDepth Q j
    have hpoint (R : TriadicCube 2) (hR : R ∈ D) :
        vecNormSq (forcedSource_feedback_shift Q j R hEll F) ≤
          w * (q ^ j * H) ^ 2 * forcedSourceCircleEnergy R F := by
      have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
        hEll.mono (measurableSet_openCubeSet R)
          (openCubeSet_subset_of_mem_descendantsAtDepth hR)
      have hFR : MemLp F 2 (normalizedCubeMeasure R) :=
        hilbert_memLp_descendant hR hF
      have hFposR (i : Fin 2) :=
        forcedSource_positiveSeries_onDescendant Q j hFpos R hR i
      have hlocal := forcedSource_sourceShift_norm_le R hEllR hFR hFposR
      have hHist := forcedSource_inverseHistory_descendant_le Q R j hEll hR
      have hHistRnonneg : 0 ≤ lemmaVInverseHistory R a q :=
        lemmaVInverseHistory_nonneg R a hq
      have hpow : 0 ≤ q ^ j := pow_nonneg (by positivity) j
      have hHistSq : (lemmaVInverseHistory R a q) ^ 2 ≤ (q ^ j * H) ^ 2 :=
        (sq_le_sq₀ hHistRnonneg (mul_nonneg hpow hHnonneg)).2 hHist
      have hcircleR : 0 ≤ forcedSourceCircleEnergy R F :=
        forcedSourceCircleEnergy_nonneg R F
      have hlocal' : vecNormSq (forcedSource_feedback_shift Q j R hEll F) ≤
          w * (lemmaVInverseHistory R a q) ^ 2 * forcedSourceCircleEnergy R F := by
        have hRmem : R ∈ descendantsAtDepth Q j := by simpa [D] using hR
        simpa [forcedSource_feedback_shift, hRmem, w, q, H] using hlocal
      have hpointBound : vecNormSq (forcedSource_feedback_shift Q j R hEll F) ≤
          w * (q ^ j * H) ^ 2 * forcedSourceCircleEnergy R F := by
        calc
          vecNormSq (forcedSource_feedback_shift Q j R hEll F) ≤
              w * (lemmaVInverseHistory R a q) ^ 2 * forcedSourceCircleEnergy R F := hlocal'
          _ = (w * forcedSourceCircleEnergy R F) *
                (lemmaVInverseHistory R a q) ^ 2 := by ring
          _ ≤ (w * forcedSourceCircleEnergy R F) * (q ^ j * H) ^ 2 :=
            mul_le_mul_of_nonneg_left hHistSq (mul_nonneg hw0 hcircleR)
          _ = w * (q ^ j * H) ^ 2 * forcedSourceCircleEnergy R F := by ring
      exact hpointBound
    have hAvg : descendantsAverage Q j (fun R =>
        vecNormSq (forcedSource_feedback_shift Q j R hEll F)) ≤
        w * H ^ 2 * forcedSourceCircleEnergy Q F := by
      unfold descendantsAverage
      calc
        _ ≤ ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth Q j,
              (w * (q ^ j * H) ^ 2 * forcedSourceCircleEnergy R F) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun R hR => hpoint R hR
        _ = w * (q ^ j * H) ^ 2 *
            descendantsAverage Q j (fun R => forcedSourceCircleEnergy R F) := by
          unfold descendantsAverage
          rw [← Finset.mul_sum]
          ring
        _ ≤ w * (q ^ j * H) ^ 2 * (w ^ j * forcedSourceCircleEnergy Q F) := by
          apply mul_le_mul_of_nonneg_left
            (by simpa [w] using forcedSource_circleRestriction_le Q j hFpos)
            (mul_nonneg hw0 (sq_nonneg _))
        _ = w * H ^ 2 * forcedSourceCircleEnergy Q F := by
          have hpow : (q ^ j) ^ 2 * w ^ j = 1 := by
            calc
              (q ^ j) ^ 2 * w ^ j = (q ^ 2) ^ j * w ^ j := by
                rw [pow_two, ← mul_pow, pow_two]
              _ = (q ^ 2 * w) ^ j := by rw [← mul_pow]
              _ = 1 := by rw [hq2w, one_pow]
          calc
            w * (q ^ j * H) ^ 2 * (w ^ j * forcedSourceCircleEnergy Q F) =
                w * H ^ 2 * ((q ^ j) ^ 2 * w ^ j) * forcedSourceCircleEnergy Q F := by
              rw [mul_pow]
              ring
            _ = _ := by rw [hpow]; ring
    simpa [L, forcedSource_feedback_shiftLevel] using hAvg
  have hgeom : Summable (fun j : ℕ => w ^ j) :=
    summable_geometric_of_lt_one hw0 hwle
  have hdom (j : ℕ) : 0 ≤ w ^ j * L j := mul_nonneg (pow_nonneg hw0 j) (hLnonneg j)
  have hbound (j : ℕ) : w ^ j * L j ≤
      w ^ j * (w * H ^ 2 * forcedSourceCircleEnergy Q F) :=
    mul_le_mul_of_nonneg_left (hLbound j) (pow_nonneg hw0 j)
  have hsL : Summable (fun j : ℕ => w ^ j * L j) :=
    Summable.of_nonneg_of_le hdom hbound
      (hgeom.mul_right (w * H ^ 2 * forcedSourceCircleEnergy Q F))
  have htsum := hsL.tsum_le_tsum hbound
    (hgeom.mul_right (w * H ^ 2 * forcedSourceCircleEnergy Q F))
  have hgeomEq : (∑' j : ℕ, w ^ j) = (1 - w)⁻¹ :=
    tsum_geometric_of_lt_one hw0 hwle
  have hcoef : 0 ≤ 1 - w := hwfactor
  refine ⟨?_, ?_⟩
  · simpa [L, w, q] using hsL
  · calc
      (1 - w) * (∑' j : ℕ, w ^ j * L j) ≤
          (1 - w) * (∑' j : ℕ,
            w ^ j * (w * H ^ 2 * forcedSourceCircleEnergy Q F)) :=
        mul_le_mul_of_nonneg_left htsum hcoef
      _ = w * H ^ 2 * forcedSourceCircleEnergy Q F := by
        rw [tsum_mul_right, hgeomEq]
        field_simp [ne_of_gt (sub_pos.mpr hwle)]

/-- The first potential of the actual complementary projection of a pure
second-coordinate load obeys the corrected half-gain estimate. The coefficient
comparison with `1.260` is stated separately below. -/
theorem projectedSource_forced_feedback_bound (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hFpos : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => F x i))))
    (v : H10Function (openCubeSet Q))
    (hv : (fun x => (projectedSourceField Q ν σ hν hσ k hF x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] v.toH1Function.grad) :
    Real.sqrt (vectorWeakHaarEnergy Q
      (fun x i => v.toH1Function.grad x i)) ≤
      (1 / 2 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) *
        lemmaVInverseHistory Q (responseFramePlanarCoefficientField ν σ k)
          ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        Real.sqrt (vectorPositiveHaarEnergy Q F) := by
  let U := openCubeSet Q
  let a := responseFramePlanarCoefficientField ν σ k
  let Y := projectedSourceCompatibleState Q ν σ hν hσ k hF
  let Z := projectedSourceField Q ν σ hν hσ k hF
  let W : BlockState 2 := ⟨fun x => (Z x).1, fun x => (Z x).2⟩
  let D := scalarFrameRealization Q ν σ hν hσ k
  let E0 := D.energyBilin
    (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
    (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF))
  let E := blockPairingAverage U a Y Y
  let V : Vec 2 → Vec 2 := fun x i => v.toH1Function.grad x i
  let G : Vec 2 → Vec 2 := Y.potential
  let q : ℝ := Real.sqrt 3
  let w : ℝ := q⁻¹
  let B : ℝ := lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ))
  let B0 : ℝ := lemmaVInverseHistory Q a q
  let P : ℝ := vectorPositiveHaarEnergy Q F
  let Gweak : ℝ := vectorWeakHaarEnergy Q G
  let meanV : TriadicCube 2 → Vec 2 := fun R i => cubeAverage R (fun x => V x i)
  let meanG : TriadicCube 2 → Vec 2 := fun R i => cubeAverage R (fun x => G x i)
  let Glevel : ℕ → ℝ := fun j => forcedSource_meanLevel Q j G
  let Vlevel : ℕ → ℝ := fun j => forcedSource_meanLevel Q j V
  have hq : 1 < q := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hwpos : 0 < w := by dsimp [w]; positivity
  have hw0 : 0 ≤ w := hwpos.le
  have hwle : w < 1 := (inv_lt_one₀ (lt_trans zero_lt_one hq)).2 hq
  have hwfactor : 0 ≤ 1 - w := by linarith
  have hEll : IsEllipticFieldOn (ν / σ)
      (((ν / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (ν / σ)) U a := by
    simpa [U, a] using responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) ν σ hν hσ k
  let Slevel : ℕ → ℝ := fun j => descendantsAverage Q j (fun R => vecNormSq
    (meanV R + forcedSource_feedback_shift Q j R hEll F))
  let Tweak : ℝ := (1 - w) * ∑' j : ℕ, w ^ j *
    forcedSource_feedback_shiftLevel Q j hEll F
  let Sweak : ℝ := (1 - w) * ∑' j : ℕ, w ^ j * Slevel j
  let forcedSourceFeedbackFiniteMeasure : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hFvec : MemVectorL2 U F :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hFcoord (i : Fin 2) :
      MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) := by
    exact memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 hFvec i)
  have hCompat := projectedSourceCompatibleState_compatible Q ν σ hν hσ k hF
  have hYmem : MemBlockL2 U Y.eval := by
    simpa [Y] using hCompat.1
  have hYpot : IsPotentialOn U Y.potential := by
    change IsPotentialOn U (fun x => (Y.eval x).1)
    simpa [Y, projectedSourceCompatibleState, projectedSourceField, Z, W, a, U,
      BlockState.eval] using hCompat.2.1
  have hYsol : IsSolenoidalOn U Y.flux := by
    change IsSolenoidalOn U (fun x => (Y.eval x).2)
    simpa [Y, projectedSourceCompatibleState, projectedSourceField, Z, W, a, U,
      BlockState.eval] using hCompat.2.2
  obtain ⟨g, hg⟩ := hYpot
  have hGcoord (i : Fin 2) :
      MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q) := by
    simpa [G, hg] using g.grad_memL2_normalizedCubeMeasure i
  have hZmem : MemBlockL2 U (fun x => Z x) := Lp.memLp Z
  have hZeq : toHilbertBlockL2OfBlockField hZmem =
      scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF) := by
    change toHilbertBlockL2OfBlockField
      (Lp.memLp (hilbertBlockL2ToBlockL2
        (scalarProjectionResidual Q ν σ hν hσ k (projectedSourceLoad Q hF)))) = _
    exact hilbert_field_rebuild _
  have hWeval : W.eval = fun x => Z x := by
    funext x
    exact Prod.eta _
  have hbil := scalar_frame_bilinear_field Q ν σ hν hσ k hZmem hZmem
  rw [hZeq] at hbil
  have hblockE : blockPairingAverage U a W W = E0 := by
    change volumeAverage U (fun x => blockVecDot (W.eval x)
      (blockMatVecMul (blockCoeffField a x) (W.eval x))) = _
    rw [hWeval]
    exact hbil.symm
  have hreflectE : E = blockPairingAverage U a W W := by
    dsimp [E]
    change blockPairingAverage U a (pairedReflectState a W)
      (pairedReflectState a W) = blockPairingAverage U a W W
    exact pairedReflect_pairingAverage_isometry hEll W W
  have hsourcePair := projectedSource_energy_eq_pairing Q ν σ hν hσ k hF
  have hsourcePair' : E0 = vectorPairing Q F G := by
    simpa [E0, D, G, Y] using hsourcePair
  have hEpair : E = vectorPairing Q F G := hreflectE.trans (hblockE.trans hsourcePair')
  have hEnonneg : 0 ≤ E := by
    simpa [E] using compatible_blockPairingAverage_nonneg hEll Y
  have hIntOpen : IntegrableOn (blockPairingIntegrand a Y Y) U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      hYmem hYmem hEll
  have hInt : IntegrableOn (blockPairingIntegrand a Y Y) (cubeSet Q) :=
    integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr hIntOpen
  have hErootCube : cubeAverage Q (blockPairingIntegrand a Y Y) = E := by
    rw [cubeAverage_eq_integralAverage_openCubeSet Q]
    rfl
  have hEnergyAverage (j : ℕ) :
      descendantsAverage Q j (fun R => cubeAverage R (blockPairingIntegrand a Y Y)) =
        cubeAverage Q (blockPairingIntegrand a Y Y) := by
    exact (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j
      (blockPairingIntegrand a Y Y) hInt).symm
  have hVSeries : Summable (fun j : ℕ => w ^ j * Vlevel j) := by
    simpa [w, q, Vlevel] using forcedSource_meanLevel_series_summable Q
      (fun i => v.toH1Function.grad_memL2_normalizedCubeMeasure i)
  have hGSeries : Summable (fun j : ℕ => w ^ j * Glevel j) := by
    simpa [w, q, Glevel] using forcedSource_meanLevel_series_summable Q hGcoord
  have hVWeakEq : vectorWeakHaarEnergy Q V =
      (1 - w) * ∑' j : ℕ, w ^ j * Vlevel j := by
    simpa [w, q, Vlevel] using forcedSource_weakEnergy_eq_meanSeries Q
      (fun i => v.toH1Function.grad_memL2_normalizedCubeMeasure i)
  have hGWeakEq : Gweak = (1 - w) * ∑' j : ℕ, w ^ j * Glevel j := by
    simpa [w, q, Gweak, Glevel] using forcedSource_weakEnergy_eq_meanSeries Q hGcoord
  have hVnonneg (j : ℕ) : 0 ≤ Vlevel j := by
    unfold Vlevel forcedSource_meanLevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  have hGlevNonneg (j : ℕ) : 0 ≤ Glevel j := by
    unfold Glevel forcedSource_meanLevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  have hGweakNonneg : 0 ≤ Gweak := vectorWeakHaarEnergy_nonneg Q G
  have hPnonneg : 0 ≤ P := vectorPositiveHaarEnergy_nonneg Q F
  have hBnonneg : 0 ≤ B := by
    dsimp [B, a]
    exact lemmaVInverseHistory_nonneg Q (responseFramePlanarCoefficientField ν σ k)
      (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hB0nonneg : 0 ≤ B0 := by
    dsimp [B0]
    exact lemmaVInverseHistory_nonneg Q a hq
  have hqQuarter : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hqCompare : (3 : ℝ) ^ (1 / 4 : ℝ) ≤ q := by
    calc
      (3 : ℝ) ^ (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = q := by dsimp [q]; exact (Real.sqrt_eq_rpow 3).symm
  have hinvCompare : q⁻¹ ≤ ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr hqCompare
  have hHistoryCompare : B0 ≤ B := by
    exact lemmaVInverseHistory_le_of_inverse_discount Q hEll hq hqQuarter hinvCompare
  have hHsum : Summable (fun j : ℕ => w ^ j * lemmaVInverseDepthMax Q a j) := by
    simpa [w, q] using lemmaVInverseHistory_summable Q hEll hq
  let M : ℕ → ℝ := lemmaVInverseDepthMax Q a
  let Slevel' : ℕ → ℝ := fun j => descendantsAverage Q j (fun R => vecNormSq
    (meanV R + forcedSource_feedback_shift Q j R hEll F))
  have hSlevelEq : Slevel = Slevel' := by
    funext j
    rfl
  have hGlevelEq : Glevel = fun j => descendantsAverage Q j (fun R => vecNormSq (meanG R)) := by
    funext j
    rfl
  have hVlevelEq : Vlevel = fun j => descendantsAverage Q j (fun R => vecNormSq (meanV R)) := by
    funext j
    rfl
  have hpoint (j : ℕ) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q j) :
      vecNormSq (meanG R) + vecNormSq
          (meanV R + forcedSource_feedback_shift Q j R hEll F) ≤
        M j * cubeAverage R (blockPairingIntegrand a Y Y) := by
    let Vset := openCubeSet R
    let forcedSourceDescendantFiniteMeasure : IsFiniteMeasure (volumeMeasureOn Vset) :=
      (isOpenBoundedConvexDomain_openCubeSet R).isFiniteMeasure_restrict_volume
    have hRQ : Vset ⊆ U := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hEllR : IsEllipticFieldOn (ν / σ)
        (((ν / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (ν / σ)) Vset a :=
      hEll.mono (measurableSet_openCubeSet R) hRQ
    have hYmemR : MemBlockL2 Vset Y.eval :=
      hYmem.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hYpotentialMemR : MemVectorL2 Vset Y.potential :=
      memVectorL2_fst_of_memBlockL2 hYmemR
    have hYfluxMemR : MemVectorL2 Vset Y.flux :=
      memVectorL2_snd_of_memBlockL2 hYmemR
    have hGmemR : MemVectorL2 Vset g.grad := by
      simpa only [← hg] using hYpotentialMemR
    have hYpotR : IsBlockPotentialOn Vset Y := by
      change IsPotentialOn Vset Y.potential
      simpa only [hg] using g.isPotentialOn.restrict_of_isOpen_of_memVectorL2
        (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hRQ hGmemR
    have hYsolR : IsBlockSolenoidalOn Vset Y := by
      change IsSolenoidalOn Vset Y.flux
      exact hYsol.restrict_of_isOpen_of_memVectorL2
        (isOpen_openCubeSet Q) (isOpen_openCubeSet R) hRQ hYfluxMemR
    have hFmemR : MemVectorL2 Vset F :=
      hFvec.mono_measure (Measure.restrict_mono_set volume hRQ)
    have hZfirstR : MemVectorL2 Vset (fun x => (Z x).1) :=
      (memVectorL2_fst_of_memBlockL2 hZmem).mono_measure
        (Measure.restrict_mono_set volume hRQ)
    have hImageAE : (fun x => (blockMatVecMul (blockCoeffField a x)
          (Y.eval x)).2) =ᵐ[volumeMeasureOn Vset] fun x => (Z x).1 := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      have hact := pairedReflectState_action hEll W (hRQ hx)
      have hact' : blockMatVecMul (blockCoeffField a x) (Y.eval x) = (Z x).swap := by
        simpa [Y, Z, W, projectedSourceCompatibleState, projectedSourceField,
          BlockState.eval, a, U] using hact
      exact congrArg Prod.snd hact'
    have hImageMemR : MemVectorL2 Vset
        (fun x => (blockMatVecMul (blockCoeffField a x) (Y.eval x)).2) :=
      (memLp_congr_ae hImageAE).2 hZfirstR
    have hforcedR (T : BlockState 2)
        (hT : ScalarVariation Vset T.eval) :
        volumeAverage Vset (blockPairingIntegrand a T Y) =
          volumeAverage Vset (fun x => vecDot (T.potential x) (F x)) := by
      have hI := projectedSource_forcedResponse_onDescendant Q j ν σ hν hσ k hF R hR T hT
      have hI' : ∫ x in Vset, blockPairingIntegrand a T Y x ∂volume =
          ∫ x in Vset, vecDot (T.potential x) (F x) ∂volume := by
        simpa [Vset, a, Y, projectedSourceCompatibleState, projectedSourceField] using hI
      unfold volumeAverage
      rw [hI']
    have hlocal := forcedSource_local_paired_euclidean hEllR Y hYpotR hYsolR
      hYmemR hImageMemR hFmemR hforcedR
    have hpotMean : pairedPotentialMean Vset Y = meanG R := by
      calc
        pairedPotentialMean Vset Y = volumeAverageVec Vset Y.potential := rfl
        _ = volumeAverageVec Vset g.grad :=
          forcedSource_volumeAverageVec_congr_ae
            (Filter.Eventually.of_forall fun x => congrFun hg.symm x)
        _ = meanG R := by
          funext i
          change volumeAverage (openCubeSet R) (fun x => g.grad x i) =
            cubeAverage R (fun x => Y.potential x i)
          rw [forcedSource_volumeAverage_eq_cubeAverage]
          apply congrArg (cubeAverage R)
          funext x
          exact congrArg (fun z : Vec 2 => z i) (congrFun hg x)
    have hvR : (fun x => (Z x).1) =ᵐ[volumeMeasureOn Vset] (fun x => V x) :=
      ae_restrict_of_ae_restrict_of_subset hRQ hv
    have hFluxAE : (fun x => (blockMatVecMul (blockCoeffField a x)
          (Y.eval x)).2) =ᵐ[volumeMeasureOn Vset] V := hImageAE.trans hvR
    have hfluxMean : pairedFluxImageMean Vset a Y = meanV R := by
      calc
        pairedFluxImageMean Vset a Y = volumeAverageVec Vset
            (fun x => (blockMatVecMul (blockCoeffField a x) (Y.eval x)).2) := rfl
        _ = volumeAverageVec Vset V := forcedSource_volumeAverageVec_congr_ae hFluxAE
        _ = meanV R := by
          funext i
          change volumeAverage (openCubeSet R) (fun x => V x i) =
            cubeAverage R (fun x => V x i)
          exact forcedSource_volumeAverage_eq_cubeAverage R (fun x => V x i)
    have hpairAvg : blockPairingAverage Vset a Y Y =
        cubeAverage R (blockPairingIntegrand a Y Y) := by
      rw [blockPairingAverage, cubeAverage_eq_integralAverage_openCubeSet]
      rfl
    have hlocalMean : vecNormSq (meanG R) + vecNormSq
        (meanV R + forcedSource_feedback_shift Q j R hEll F) ≤
        Book.Ch02.matrixNorm (coarseBlockMatrix Vset a).lowerRight *
          cubeAverage R (blockPairingIntegrand a Y Y) := by
      have hshift : forcedSource_feedback_shift Q j R hEll F =
          pairedBesselSourceCorrectionVector hEllR F := by
        simp [forcedSource_feedback_shift, hR]
      simpa [Vset, hpotMean, hfluxMean, hshift, hpairAvg] using hlocal
    have hvolR : 0 < (MeasureTheory.volume (openCubeSet R)).toReal := by
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos R
    obtain ⟨_, hCoarseR, _, _, _, _, _, _⟩ :=
      exists_energyMap_coarseData (isOpenBoundedConvexDomain_openCubeSet R) hEllR hvolR
    have hsup : Book.Ch02.matrixNorm (coarseBlockMatrix Vset a).lowerRight ≤ M j := by
      have hsup' : Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) a) ≤ M j := by
        unfold M lemmaVInverseDepthMax Book.Ch02.finsetSupReal
        exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨R, hR, rfl⟩
      simpa [Vset, coarseBlockMatrix_lowerRight_eq_of_isCoarseBlockMatrix hCoarseR] using hsup'
    have henergyR : 0 ≤ cubeAverage R (blockPairingIntegrand a Y Y) := by
      rw [← hpairAvg]
      exact compatible_blockPairingAverage_nonneg hEllR Y
    calc
      _ ≤ Book.Ch02.matrixNorm (coarseBlockMatrix Vset a).lowerRight *
          cubeAverage R (blockPairingIntegrand a Y Y) := hlocalMean
      _ ≤ M j * cubeAverage R (blockPairingIntegrand a Y Y) :=
        mul_le_mul_of_nonneg_right hsup henergyR
  have hLevel (j : ℕ) : Slevel j + Glevel j ≤ M j * E := by
    have hsumDef : Slevel j + Glevel j = descendantsAverage Q j (fun R =>
        vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll F) +
          vecNormSq (meanG R)) := by
      unfold Slevel Glevel forcedSource_meanLevel
      dsimp [meanV, meanG]
      rw [descendantsAverage_add]
    have hAvgBound : descendantsAverage Q j (fun R =>
        vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll F) +
          vecNormSq (meanG R)) ≤ M j *
        descendantsAverage Q j (fun R => cubeAverage R (blockPairingIntegrand a Y Y)) := by
      unfold descendantsAverage
      calc
        ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth Q j,
              (vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll F) +
                vecNormSq (meanG R)) ≤
          ((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth Q j,
              (M j * cubeAverage R (blockPairingIntegrand a Y Y)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum fun R hR => by
              simpa [add_comm] using hpoint j R hR
        _ = M j * (((descendantsAtDepth Q j).card : ℝ)⁻¹ *
            ∑ R ∈ descendantsAtDepth Q j,
              cubeAverage R (blockPairingIntegrand a Y Y)) := by
            rw [← Finset.mul_sum]
            ring
        _ = M j * descendantsAverage Q j
            (fun R => cubeAverage R (blockPairingIntegrand a Y Y)) := by rfl
    calc
      Slevel j + Glevel j = _ := hsumDef
      _ ≤ M j * descendantsAverage Q j
          (fun R => cubeAverage R (blockPairingIntegrand a Y Y)) := hAvgBound
      _ = M j * E := by rw [hEnergyAverage j, hErootCube]
  have hSnonneg (j : ℕ) : 0 ≤ Slevel j := by
    unfold Slevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  let Mseries := lemmaVInverseHistory_summable Q hEll hq
  have hMseries : Summable (fun j : ℕ => w ^ j * M j) := by
    simpa [M, w, q] using Mseries
  have hMmul : Summable (fun j : ℕ => w ^ j * (M j * E)) := by
    simpa [mul_assoc] using hMseries.mul_right E
  have hJointDom (j : ℕ) : 0 ≤ w ^ j * (Slevel j + Glevel j) :=
    mul_nonneg (pow_nonneg hw0 j) (add_nonneg (hSnonneg j) (hGlevNonneg j))
  have hJointBound (j : ℕ) : w ^ j * (Slevel j + Glevel j) ≤
      w ^ j * (M j * E) :=
    mul_le_mul_of_nonneg_left (hLevel j) (pow_nonneg hw0 j)
  have hJointSeries : Summable (fun j : ℕ => w ^ j * (Slevel j + Glevel j)) :=
    Summable.of_nonneg_of_le hJointDom hJointBound hMmul
  have hSdom (j : ℕ) : 0 ≤ w ^ j * Slevel j :=
    mul_nonneg (pow_nonneg hw0 j) (hSnonneg j)
  have hSbound (j : ℕ) : w ^ j * Slevel j ≤ w ^ j * (Slevel j + Glevel j) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hw0 j)
    linarith [hGlevNonneg j]
  have hSseries : Summable (fun j : ℕ => w ^ j * Slevel j) :=
    Summable.of_nonneg_of_le hSdom hSbound hJointSeries
  have hsplit : (∑' j : ℕ, w ^ j * Slevel j) +
        (∑' j : ℕ, w ^ j * Glevel j) =
      ∑' j : ℕ, w ^ j * (Slevel j + Glevel j) := by
    rw [← hSseries.tsum_add hGSeries]
    apply tsum_congr
    intro j
    ring
  have hJointTsum := hJointSeries.tsum_le_tsum hJointBound hMmul
  have hB0Compare :
      (1 - w) * ∑' j : ℕ, w ^ j * M j = B0 := by
    rfl
  have hB0mul :
      (1 - w) * (∑' j : ℕ, w ^ j * (M j * E)) = B0 * E := by
    have hTmul : (∑' j : ℕ, w ^ j * (M j * E)) =
        (∑' j : ℕ, w ^ j * M j) * E := by
      calc
        _ = ∑' j : ℕ, (w ^ j * M j) * E := by
          apply tsum_congr
          intro j
          ring
        _ = _ := tsum_mul_right
    rw [hTmul, ← hB0Compare]
    ring
  have hJoint : Sweak + Gweak ≤ B * E := by
    calc
      Sweak + Gweak = (1 - w) *
          ((∑' j : ℕ, w ^ j * Slevel j) +
            (∑' j : ℕ, w ^ j * Glevel j)) := by
              rw [hGWeakEq]
              dsimp [Sweak]
              ring
      _ = (1 - w) * ∑' j : ℕ, w ^ j * (Slevel j + Glevel j) := by rw [hsplit]
      _ ≤ (1 - w) * ∑' j : ℕ, w ^ j * (M j * E) :=
        mul_le_mul_of_nonneg_left hJointTsum hwfactor
      _ = B0 * E := hB0mul
      _ ≤ B * E := mul_le_mul_of_nonneg_right hHistoryCompare hEnonneg
  have hGduality : E ≤ Real.sqrt P * Real.sqrt Gweak := by
    have hdual := abs_vectorPairing_le_vectorPositiveHaarNorm_mul_vectorWeakHaarNorm
      Q hFcoord hGcoord hFpos
    rw [← hEpair] at hdual
    have hdual' : |E| ≤ Real.sqrt P * Real.sqrt Gweak := by
      simpa [P, Gweak, vectorPositiveHaarNorm, vectorWeakHaarNorm] using hdual
    exact (abs_le.mp hdual').2
  let X : ℝ := Real.sqrt Sweak
  let Gnorm : ℝ := Real.sqrt Gweak
  have hSweakNonneg : 0 ≤ Sweak := by
    dsimp [Sweak]
    apply mul_nonneg hwfactor
    exact tsum_nonneg fun j => mul_nonneg (pow_nonneg hw0 j) (hSnonneg j)
  have hJointNorm : X ^ 2 + Gnorm ^ 2 ≤ B * Real.sqrt P * Gnorm := by
    calc
      X ^ 2 + Gnorm ^ 2 = Sweak + Gweak := by
        rw [Real.sq_sqrt hSweakNonneg, Real.sq_sqrt hGweakNonneg]
      _ ≤ B * E := hJoint
      _ ≤ B * (Real.sqrt P * Gnorm) :=
        mul_le_mul_of_nonneg_left hGduality hBnonneg
      _ = B * Real.sqrt P * Gnorm := by ring
  have hHalf : X ≤ B * Real.sqrt P / 2 :=
    forcedSource_half_gain_of_joint_energy hBnonneg (Real.sqrt_nonneg P) hJointNorm
  have hShiftData := forcedSource_feedback_shift_weakEnergy_le Q hEll hF hFpos
  have hTweakBound : Tweak ≤ w * B ^ 2 * forcedSourceCircleEnergy Q F := by
    simpa [Tweak, w, B, q] using hShiftData.2
  have hTweakNonneg : 0 ≤ Tweak := by
    dsimp [Tweak]
    apply mul_nonneg hwfactor
    apply tsum_nonneg
    intro j
    apply mul_nonneg (pow_nonneg hw0 j)
    unfold forcedSource_feedback_shiftLevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  let α : ℝ := (Real.sqrt (Real.sqrt 3))⁻¹
  have hAlphaNonneg : 0 ≤ α := by dsimp [α]; positivity
  have hAlphaSq : α ^ 2 = w := by
    dsimp [α, w, q]
    calc
      (Real.sqrt (Real.sqrt 3))⁻¹ ^ 2 =
          ((Real.sqrt (Real.sqrt 3)) ^ 2)⁻¹ := by rw [← inv_pow]
      _ = (Real.sqrt 3)⁻¹ := by rw [Real.sq_sqrt (Real.sqrt_nonneg 3)]
  have hAlphaRoot : Real.sqrt w = α := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg w) hAlphaNonneg).1
    calc
      (Real.sqrt w) ^ 2 = w := Real.sq_sqrt hw0
      _ = α ^ 2 := hAlphaSq.symm
  have hTroot : Real.sqrt Tweak ≤ Real.sqrt w * B *
      Real.sqrt (forcedSourceCircleEnergy Q F) := by
    have hradEq : Real.sqrt (w * B ^ 2 * forcedSourceCircleEnergy Q F) =
        Real.sqrt w * B * Real.sqrt (forcedSourceCircleEnergy Q F) := by
      calc
        Real.sqrt (w * B ^ 2 * forcedSourceCircleEnergy Q F) =
            Real.sqrt (w * (B ^ 2 * forcedSourceCircleEnergy Q F)) := by ring_nf
        _ = Real.sqrt w * Real.sqrt (B ^ 2 * forcedSourceCircleEnergy Q F) :=
          Real.sqrt_mul hw0 _
        _ = Real.sqrt w * (Real.sqrt (B ^ 2) *
              Real.sqrt (forcedSourceCircleEnergy Q F)) := by
          rw [Real.sqrt_mul (sq_nonneg B)]
        _ = Real.sqrt w * B * Real.sqrt (forcedSourceCircleEnergy Q F) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hBnonneg]
          ring
    rw [← hradEq]
    exact Real.sqrt_le_sqrt hTweakBound
  have hCircleLE : forcedSourceCircleEnergy Q F ≤ P := by
    have hdecomp : P =
        (∑ i : Fin 2, energy Q (cubeIncrement Q 0 (fun x => F x i))) +
          forcedSourceCircleEnergy Q F := by
      unfold P vectorPositiveHaarEnergy forcedSourceCircleEnergy primalEnergy
      rw [Finset.sum_add_distrib]
    have hroot : 0 ≤ ∑ i : Fin 2, energy Q
        (cubeIncrement Q 0 (fun x => F x i)) :=
      Finset.sum_nonneg fun i _ => energy_nonneg Q _
    linarith [hdecomp]
  have hShift : Real.sqrt Tweak ≤ α * B * Real.sqrt P := by
    calc
      Real.sqrt Tweak ≤ Real.sqrt w * B *
          Real.sqrt (forcedSourceCircleEnergy Q F) := hTroot
      _ = α * B * Real.sqrt (forcedSourceCircleEnergy Q F) := by rw [hAlphaRoot]
      _ ≤ α * B * Real.sqrt P :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hCircleLE)
          (mul_nonneg hAlphaNonneg hBnonneg)
  let c : ℕ → ℝ := fun j => (1 - w) * w ^ j
  have hVsumSq (j : ℕ) : 0 ≤ c j * Vlevel j :=
    mul_nonneg (mul_nonneg hwfactor (pow_nonneg hw0 j)) (hVnonneg j)
  have hSsumSq (j : ℕ) : 0 ≤ c j * Slevel j :=
    mul_nonneg (mul_nonneg hwfactor (pow_nonneg hw0 j)) (hSnonneg j)
  have hTsumSq (j : ℕ) : 0 ≤ c j * forcedSource_feedback_shiftLevel Q j hEll F := by
    apply mul_nonneg (mul_nonneg hwfactor (pow_nonneg hw0 j))
    unfold forcedSource_feedback_shiftLevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  let av : ℕ → ℝ := fun j => Real.sqrt (c j * Vlevel j)
  let as : ℕ → ℝ := fun j => Real.sqrt (c j * Slevel j)
  let aShift : ℕ → ℝ := fun j =>
    Real.sqrt (c j * forcedSource_feedback_shiftLevel Q j hEll F)
  have hav : Summable (fun j : ℕ => (av j) ^ 2) := by
    have h := hVSeries.mul_left (1 - w)
    have heq : (fun j => (av j) ^ 2) =
        (fun j => (1 - w) * (w ^ j * Vlevel j)) := by
      funext j
      dsimp [av, c]
      rw [Real.sq_sqrt (hVsumSq j)]
      ring
    rw [heq]
    exact h
  have has : Summable (fun j : ℕ => (as j) ^ 2) := by
    have h := hSseries.mul_left (1 - w)
    have heq : (fun j => (as j) ^ 2) =
        (fun j => (1 - w) * (w ^ j * Slevel j)) := by
      funext j
      dsimp [as, c]
      rw [Real.sq_sqrt (hSsumSq j)]
      ring
    rw [heq]
    exact h
  have hat : Summable (fun j : ℕ => (aShift j) ^ 2) := by
    have h := hShiftData.1.mul_left (1 - w)
    have heq : (fun j => (aShift j) ^ 2) =
        (fun j => (1 - w) * (w ^ j * forcedSource_feedback_shiftLevel Q j hEll F)) := by
      funext j
      dsimp [aShift, c]
      rw [Real.sq_sqrt (hTsumSq j)]
      ring
    rw [heq]
    simpa [w] using h
  have hLevelTriangle (j : ℕ) :
      Real.sqrt (Vlevel j) ≤ Real.sqrt (Slevel j) +
        Real.sqrt (forcedSource_feedback_shiftLevel Q j hEll F) := by
    have hagg := sqrt_descendantsAverage_energy_bound_three Q j
      (fun R => vecNormSq (meanV R))
      (fun R => vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll F))
      (fun R => vecNormSq (forcedSource_feedback_shift Q j R hEll F))
      (fun _ => 0) (A := 1) (B := 1) (C := 0)
      (by norm_num) (by norm_num) (by norm_num)
      (fun R hR => vecNormSq_nonneg _)
      (fun R hR => vecNormSq_nonneg _)
      (fun R hR => vecNormSq_nonneg _)
      (fun R hR => by simp)
      (fun R hR => by
        simpa using forcedSource_sqrt_vecNormSq_sub_le
          (meanV R) (forcedSource_feedback_shift Q j R hEll F))
    simpa [Vlevel, Slevel, forcedSource_meanLevel, forcedSource_feedback_shiftLevel] using hagg
  have hab (j : ℕ) : av j ≤ as j + aShift j := by
    have hc : 0 ≤ c j := mul_nonneg hwfactor (pow_nonneg hw0 j)
    change Real.sqrt (c j * Vlevel j) ≤
      Real.sqrt (c j * Slevel j) +
        Real.sqrt (c j * forcedSource_feedback_shiftLevel Q j hEll F)
    calc
      Real.sqrt (c j * Vlevel j) = Real.sqrt (c j) * Real.sqrt (Vlevel j) :=
        Real.sqrt_mul hc _
      _ ≤ Real.sqrt (c j) * (Real.sqrt (Slevel j) +
          Real.sqrt (forcedSource_feedback_shiftLevel Q j hEll F)) :=
        mul_le_mul_of_nonneg_left (hLevelTriangle j) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_mul hc, Real.sqrt_mul hc]; ring
  have htriangle := sqrt_tsum_sq_le_of_pointwise (a := as) (b := aShift) (c := av) has hat
    (fun j => Real.sqrt_nonneg _) hab
  have havEq : (∑' j : ℕ, (av j) ^ 2) = vectorWeakHaarEnergy Q V := by
    calc
      _ = (1 - w) * ∑' j : ℕ, w ^ j * Vlevel j := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro j
        dsimp [av, c]
        rw [Real.sq_sqrt (hVsumSq j)]
        ring
      _ = vectorWeakHaarEnergy Q V := hVWeakEq.symm
  have hasEq : (∑' j : ℕ, (as j) ^ 2) = Sweak := by
    dsimp [Sweak]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp [as, c]
    rw [Real.sq_sqrt (hSsumSq j)]
    ring
  have hatEq : (∑' j : ℕ, (aShift j) ^ 2) = Tweak := by
    dsimp [Tweak]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp [aShift, c]
    rw [Real.sq_sqrt (hTsumSq j)]
    ring
  have hWeakTriangle :
      Real.sqrt (vectorWeakHaarEnergy Q V) ≤ Real.sqrt Sweak + Real.sqrt Tweak := by
    rw [← havEq, ← hasEq, ← hatEq]
    exact htriangle.2
  have hHalf := forcedSource_half_gain_of_joint_energy
    hBnonneg (Real.sqrt_nonneg P) hJointNorm
  have hExact : Real.sqrt (vectorWeakHaarEnergy Q V) ≤
      (1 / 2 + α) * B * Real.sqrt P := by
    calc
      Real.sqrt (vectorWeakHaarEnergy Q V) ≤ Real.sqrt Sweak + Real.sqrt Tweak :=
        hWeakTriangle
      _ ≤ B * Real.sqrt P / 2 + α * B * Real.sqrt P := add_le_add hHalf hShift
      _ = (1 / 2 + α) * B * Real.sqrt P := by ring
  have hCoeff : 1 / 2 + α = 1 / 2 + (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    calc
      1 / 2 + α = forcedSourceD := rfl
      _ = 1 / 2 + (3 : ℝ) ^ (-(1 / 4 : ℝ)) := forcedSourceD_exact
  have hExact' := hExact
  rw [hCoeff] at hExact'
  simpa [V, a, B, P] using hExact'

/-- The corrected non-strict product bound at the safely rounded constant.
The strict comparison is the separate constant theorem
`forcedSourceD_lt_126_over_100`. -/
theorem projectedSource_forced_feedback_bound_le_126 (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) {F : Vec 2 → Vec 2}
    (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hFpos : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => F x i))))
    (v : H10Function (openCubeSet Q))
    (hv : (fun x => (projectedSourceField Q ν σ hν hσ k hF x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] v.toH1Function.grad) :
    Real.sqrt (vectorWeakHaarEnergy Q
      (fun x i => v.toH1Function.grad x i)) ≤
      (126 / 100) * lemmaVInverseHistory Q
        (responseFramePlanarCoefficientField ν σ k) ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        Real.sqrt (vectorPositiveHaarEnergy Q F) := by
  have hexact := projectedSource_forced_feedback_bound Q ν σ hν hσ k hF hFpos v hv
  let a := responseFramePlanarCoefficientField ν σ k
  let B := lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ))
  let P := vectorPositiveHaarEnergy Q F
  have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hB : 0 ≤ B := by
    dsimp [B, a]
    exact lemmaVInverseHistory_nonneg Q
      (responseFramePlanarCoefficientField ν σ k) hq
  have hP : 0 ≤ P := vectorPositiveHaarEnergy_nonneg Q F
  have hcoef : 1 / 2 + (3 : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 126 / 100 := by
    calc
      1 / 2 + (3 : ℝ) ^ (-(1 / 4 : ℝ)) = forcedSourceD :=
        forcedSourceD_exact.symm
      _ ≤ 126 / 100 := le_of_lt forcedSourceD_lt_126_over_100
  have hfactor : 0 ≤ B * Real.sqrt P := mul_nonneg hB (Real.sqrt_nonneg P)
  calc
    _ ≤ (1 / 2 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * B * Real.sqrt P := by
      simpa [a, B, P] using hexact
    _ = (1 / 2 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * (B * Real.sqrt P) := by ring
    _ ≤ (126 / 100) * (B * Real.sqrt P) :=
      mul_le_mul_of_nonneg_right hcoef hfactor
    _ = (126 / 100) * B * Real.sqrt P := by ring
    _ = _ := by simp [B, P, a]

end
end ASDExplicitGamma.Variational
