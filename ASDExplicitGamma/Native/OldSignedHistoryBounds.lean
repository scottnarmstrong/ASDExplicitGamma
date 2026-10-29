module

public import ASDExplicitGamma.Cold.ScalarCoefficient
public import ASDExplicitGamma.Inverse.ClippedMatrixSymmetricNorm
public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import Homogenization.CoarseGraining.CoarseBounds.AeBridge
public import Homogenization.CoarseGraining.CoarseBounds.Sandwich
public import Homogenization.Geometry.BoundaryLayer
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import ASDExplicitGamma.Variational.AdapterAmplitude

/-! Finiteness of the actual OLD trace-defect history under qualitative
ellipticity. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational
open scoped ENNReal

noncomputable section

private theorem old_signed_translate_ellipticity {d : ℕ} {U : Set (Vec d)}
    {a : CoeffField d} {lam Lam : ℝ} (z : Vec d)
    (hEll : IsEllipticFieldOn lam Lam (translateSet z U) a) :
    IsEllipticFieldOn lam Lam U (translateCoeffField z a) := by
  classical
  refine ⟨?_, ?_⟩
  · have hshift : Measurable (fun x : Vec d => x + z) :=
      (continuous_id.add continuous_const).measurable
    have hcomp :
        Measurable (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) :=
      hEll.1.comp hshift
    have hEq :
        (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) =
          (fun x i j => if x ∈ U then translateCoeffField z a x i j else 0) := by
      funext x i j
      have hadd_sub : x + z - z = x := by
        ext k
        simp [sub_eq_add_neg, add_assoc]
      by_cases hx : x ∈ U
      · have hxt : x + z ∈ translateSet z U := by
          rw [mem_translateSet_iff_sub_mem, hadd_sub]
          exact hx
        simp [hx, hxt]
        rfl
      · have hxt : x + z ∉ translateSet z U := by
          intro hmem
          rw [mem_translateSet_iff_sub_mem] at hmem
          rw [hadd_sub] at hmem
          exact hx hmem
        simp [hx, hxt]
    simpa [hEq] using hcomp
  · intro x hx
    have hadd_sub : x + z - z = x := by
      ext k
      simp [sub_eq_add_neg, add_assoc]
    have hxt : x + z ∈ translateSet z U := by
      rw [mem_translateSet_iff_sub_mem, hadd_sub]
      exact hx
    exact hEll.2 (x + z) hxt

private theorem old_signed_coarse_quadratic_cube_upper {Q : TriadicCube 2}
    {Θ : ℝ} {a : CoeffField 2}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet Q) a) (P : BlockVec 2) :
    blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) ≤
      2 * (Θ * vecNormSq P.1 + vecNormSq P.2) := by
  let z := triadicCubeShift Q
  let U := cubeSet (originCube 2 Q.scale)
  have hcube : cubeSet Q = translateSet z U := by
    simpa [z, U] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hEll0 : IsEllipticFieldOn 1 Θ U (translateCoeffField z a) :=
    old_signed_translate_ellipticity z (by simpa [hcube, U] using hEll)
  rw [hcube, coarseBlockMatrix_translateSet_eq_translateCoeffField]
  exact Homogenization.blockVecDot_coarseBlockMatrix_cube_le hEll0 P

private theorem old_signed_coarse_quadratic_cube_lower {Q : TriadicCube 2}
    {Θ : ℝ} {a : CoeffField 2}
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet Q) a) (P : BlockVec 2) :
    0 ≤ blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet Q) a) P) := by
  let z := triadicCubeShift Q
  let U := cubeSet (originCube 2 Q.scale)
  have hcube : cubeSet Q = translateSet z U := by
    simpa [z, U] using cubeSet_eq_translateSet_originCube_of_triadicCube Q
  have hEll0 : IsEllipticFieldOn 1 Θ U (translateCoeffField z a) :=
    old_signed_translate_ellipticity z (by simpa [hcube, U] using hEll)
  rw [hcube, coarseBlockMatrix_translateSet_eq_translateCoeffField]
  exact Homogenization.zero_le_blockVecDot_coarseBlockMatrix_cube hEll0 P

private theorem old_signed_coarse_quadratic_open_bounds (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (P : BlockVec 2) :
    0 ≤ blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) ∧
      blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) ≤
        2 * (Lam * vecNormSq P.1 + lam⁻¹ * vecNormSq P.2) := by
  classical
  have hlam : 0 < lam := (hEll.2 (cubeCenter Q) (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q))).1
  have hLam : lam ≤ Lam := (hEll.2 (cubeCenter Q) (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q))).2.1
  have hLamPos : 0 < Lam := lt_of_lt_of_le hlam hLam
  let Θ : ℝ := Lam / lam
  have hΘ : (1 : ℝ) ≤ Θ := by
    dsimp [Θ]
    exact (one_le_div₀ hlam).2 hLam
  let aN : CoeffField 2 := lam⁻¹ • a
  have hEllN : IsEllipticFieldOn 1 Θ (openCubeSet Q) aN := by
    simpa [aN, Θ, div_eq_mul_inv, mul_comm, hlam.ne'] using
      (ASDExplicitGamma.Cold.cold_isEllipticFieldOn_smul
        (inv_pos.mpr hlam) hEll)
  let U : Set (Vec 2) := openCubeSet Q
  let C : Set (Vec 2) := cubeSet Q
  let aExt : CoeffField 2 := fun x => if x ∈ U then aN x else 1
  have hmeasExt : Measurable (fun x i j => if x ∈ C then aExt x i j else 0) := by
    have hfirst : Measurable (fun x i j => if x ∈ U then aN x i j else 0) := hEllN.1
    have hsecond : Measurable (fun x i j => if x ∈ Set.diff C U then (1 : Mat 2) i j else 0) := by
      apply measurable_pi_iff.2
      intro i
      apply measurable_pi_iff.2
      intro j
      exact Measurable.ite (measurableSet_cubeSet Q |>.diff (measurableSet_openCubeSet Q))
        measurable_const measurable_const
    have heq : (fun x i j => if x ∈ C then aExt x i j else 0) =
        (fun x i j => (if x ∈ U then aN x i j else 0) +
          (if x ∈ Set.diff C U then (1 : Mat 2) i j else 0)) := by
      funext x i j
      by_cases hxU : x ∈ U
      · have hxC : x ∈ C := openCubeSet_subset_cubeSet Q hxU
        have hnotdiff : x ∉ Set.diff C U := by
          intro hd
          exact hd.2 hxU
        simp [aExt, hxU, hxC, hnotdiff]
      · by_cases hxC : x ∈ C
        · have hdiff : x ∈ Set.diff C U := ⟨hxC, hxU⟩
          simp [aExt, hxU, hxC, hdiff]
        · have hnotdiff : x ∉ Set.diff C U := by
            intro hd
            exact hxC hd.1
          simp [aExt, hxU, hxC, hnotdiff]
    rw [heq]
    exact hfirst.add hsecond
  have hEllExt : IsEllipticFieldOn 1 Θ C aExt := by
    refine ⟨hmeasExt, ?_⟩
    intro x hxC
    by_cases hxU : x ∈ U
    · simpa [aExt, hxU] using hEllN.2 x hxU
    · rw [show aExt x = 1 by simp [aExt, hxU]]
      exact Homogenization.isEllipticMatrix_one_one hΘ
  let aUn : CoeffField 2 := lam • aExt
  have hEllUn : IsEllipticFieldOn lam Lam C aUn := by
    have h := ASDExplicitGamma.Cold.cold_isEllipticFieldOn_smul hlam hEllExt
    have hLamEq : lam * (Lam * lam⁻¹) = Lam := by field_simp [hlam.ne']
    simpa [aUn, Θ, div_eq_mul_inv, hLamEq] using h
  have hnotBoundary : ∀ᵐ x ∂volume, x ∉ cubeBoundary Q := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using volume_cubeBoundary_eq_zero Q
  have hAE : aUn =ᵐ[volume.restrict C] a := by
    apply (ae_restrict_iff' (measurableSet_cubeSet Q)).2
    filter_upwards [hnotBoundary] with x hnb hxC
    have hxU : x ∈ U := by
      by_contra hxu
      exact hnb (mem_cubeBoundary_iff.mpr ⟨hxC, hxu⟩)
    have hExt : aExt x = aN x := by simp [aExt, hxU]
    have hscale : lam • aN x = a x := by
      ext i j
      simp [aN, Pi.smul_apply, hlam.ne']
    change (lam • aExt) x = a x
    rw [Pi.smul_apply, hExt, hscale]
  have hCoarse : coarseBlockMatrix C aUn = coarseBlockMatrix U a := by
    calc
      coarseBlockMatrix C aUn = coarseBlockMatrix C a :=
        coarseBlockMatrix_congr_of_ae_eq hAE
      _ = coarseBlockMatrix U a :=
        coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q a
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hs2 : (Real.sqrt lam) ^ 2 = lam := Real.sq_sqrt hlam.le
  have hRescale : coarseBlockMatrix C aUn =
      coarseMatrixRescale (Real.sqrt lam) (coarseBlockMatrix C aExt) := by
    have hcoef : aUn = (Real.sqrt lam) ^ 2 • aExt := by
      ext x i j
      simp [aUn, Pi.smul_apply, hs2]
    rw [hcoef]
    exact coarseBlockMatrix_sq_smul_triCube hEllExt hs
  have hMatrix : coarseBlockMatrix U a =
      coarseMatrixRescale (Real.sqrt lam) (coarseBlockMatrix C aExt) :=
    hCoarse.symm.trans hRescale
  have hInv : ((Real.sqrt lam)⁻¹) ^ 2 = lam⁻¹ := by
    rw [inv_pow, hs2]
  have hThetaLam : Θ * lam = Lam := by
    dsimp [Θ]
    field_simp [hlam.ne']
  have hload (P : BlockVec 2) :
      2 * (Θ * vecNormSq (loadRescale (Real.sqrt lam) P).1 +
        vecNormSq (loadRescale (Real.sqrt lam) P).2) =
      2 * (Lam * vecNormSq P.1 + lam⁻¹ * vecNormSq P.2) := by
    rcases P with ⟨p, q⟩
    simp only [loadRescale, vecNormSq_smul]
    rw [hs2, hInv]
    calc
      2 * (Θ * (lam * vecNormSq p) + lam⁻¹ * vecNormSq q) =
          2 * (Lam * vecNormSq p + lam⁻¹ * vecNormSq q) := by
        rw [← mul_assoc, hThetaLam]
      _ = 2 * (Lam * vecNormSq p + lam⁻¹ * vecNormSq q) := rfl
  have hquad (P : BlockVec 2) :
      blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) =
        blockVecDot (loadRescale (Real.sqrt lam) P)
          (blockMatVecMul (coarseBlockMatrix C aExt) (loadRescale (Real.sqrt lam) P)) := by
    rw [hMatrix]
    exact blockVecDot_coarseMatrixRescale_eq _ _ hs.ne'
  constructor
  · rw [hquad]
    exact old_signed_coarse_quadratic_cube_lower hEllExt _
  · calc
      blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) ≤
          2 * (Θ * vecNormSq (loadRescale (Real.sqrt lam) P).1 +
            vecNormSq (loadRescale (Real.sqrt lam) P).2) := by
              rw [hquad]
              exact old_signed_coarse_quadratic_cube_upper hEllExt _
      _ = 2 * (Lam * vecNormSq P.1 + lam⁻¹ * vecNormSq P.2) := hload P

private theorem old_signed_coarse_operator_norm_open_le (Q : TriadicCube 2)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    ‖HilbertBlockVec.applyBlockMat (coarseBlockMatrix (openCubeSet Q) a)‖ ≤
      2 * (Lam + lam⁻¹) := by
  have hlam : 0 < lam := (hEll.2 (cubeCenter Q) (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q))).1
  have hLam : lam ≤ Lam := (hEll.2 (cubeCenter Q) (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q))).2.1
  have hLamPos : 0 < Lam := lt_of_lt_of_le hlam hLam
  let A := coarseBlockMatrix (openCubeSet Q) a
  let T := HilbertBlockVec.applyBlockMat A
  have hSymm : IsSymmetricBlockMat A := Variational.coarseBlockMatrix_symmetric _ _
  have hT : T.IsSymmetric := by
    intro X Y
    simp only [T, HilbertBlockVec.inner_def, blockVecDot_comm]
    exact blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hSymm
      Y.toBlockVec X.toBlockVec
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  apply ciSup_le
  intro X
  by_cases hX : X = 0
  · simp [hX, T]
    positivity
  have hdenpos : 0 < ‖X‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hX)
  let P := X.toBlockVec
  have hquad := old_signed_coarse_quadratic_open_bounds Q a hEll P
  have hden : ‖X‖ ^ 2 = blockVecDot P P := HilbertBlockVec.norm_sq_eq_blockVecDot X
  have hnum : T.reApplyInnerSelf X =
      blockVecDot P (blockMatVecMul A P) := by
    have hXP : X = HilbertBlockVec.ofBlockVec P := by simp [P]
    have hinner : inner ℝ (T X) X = blockVecDot P (blockMatVecMul A P) := by
      rw [hXP]
      change inner ℝ (HilbertBlockVec.applyBlockMat A (HilbertBlockVec.ofBlockVec P))
        (HilbertBlockVec.ofBlockVec P) = _
      rw [real_inner_comm]
      simp [blockVecDot, vecDot, Fin.sum_univ_two]
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, hinner]
    simp
  have hPnonneg : 0 ≤ blockVecDot P P := by
    rw [← hden]
    positivity
  have hcap : blockVecDot P (blockMatVecMul A P) ≤
      (2 * (Lam + lam⁻¹)) * blockVecDot P P := by
    have hp := vecNormSq_nonneg P.1
    have hq := vecNormSq_nonneg P.2
    have hcoef : Lam * vecNormSq P.1 + lam⁻¹ * vecNormSq P.2 ≤
        (Lam + lam⁻¹) * (vecNormSq P.1 + vecNormSq P.2) := by
      nlinarith [mul_nonneg (inv_nonneg.mpr hlam.le) hp,
        mul_nonneg hLamPos.le hq]
    change blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) ≤
      2 * (Lam + lam⁻¹) * (vecNormSq P.1 + vecNormSq P.2)
    have hupper := hquad.2
    change blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) P) ≤
      2 * (Lam * vecNormSq P.1 + lam⁻¹ * vecNormSq P.2) at hupper
    nlinarith only [hupper, hcoef]
  have hRayPos : 0 ≤ T.rayleighQuotient X := by
    rw [ContinuousLinearMap.rayleighQuotient, hnum]
    exact div_nonneg hquad.1 (sq_nonneg ‖X‖)
  have hRayLe : T.rayleighQuotient X ≤ 2 * (Lam + lam⁻¹) := by
    rw [ContinuousLinearMap.rayleighQuotient, hnum]
    apply (div_le_iff₀ hdenpos).2
    rw [hden]
    exact hcap
  rw [abs_of_nonneg hRayPos]
  exact hRayLe

private theorem old_signed_trace_defect_open_bounds
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    0 ≤ traceDefect (openCubeSet R) a 1 ∧
      traceDefect (openCubeSet R) a 1 ≤ 4 * (Lam + lam⁻¹) := by
  classical
  have hlam : 0 < lam := (hEll.2 (cubeCenter Q) (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q))).1
  have hLam : lam ≤ Lam := (hEll.2 (cubeCenter Q) (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q))).2.1
  have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (measurableSet_openCubeSet R) hRQ
  let Θ : ℝ := Lam / lam
  have hΘ : (1 : ℝ) ≤ Θ := by
    dsimp [Θ]
    exact (one_le_div₀ hlam).2 hLam
  let aN : CoeffField 2 := lam⁻¹ • a
  have hEllN : IsEllipticFieldOn 1 Θ (openCubeSet R) aN := by
    simpa [aN, Θ, div_eq_mul_inv, mul_comm, hlam.ne'] using
      (ASDExplicitGamma.Cold.cold_isEllipticFieldOn_smul
        (inv_pos.mpr hlam) hEllR)
  let U : Set (Vec 2) := openCubeSet R
  let C : Set (Vec 2) := cubeSet R
  let aExt : CoeffField 2 := fun x => if x ∈ U then aN x else 1
  have hmeasExt : Measurable (fun x i j => if x ∈ C then aExt x i j else 0) := by
    have hfirst : Measurable (fun x i j => if x ∈ U then aN x i j else 0) := hEllN.1
    have hsecond : Measurable (fun x i j => if x ∈ Set.diff C U then (1 : Mat 2) i j else 0) := by
      apply measurable_pi_iff.2
      intro i
      apply measurable_pi_iff.2
      intro j
      exact Measurable.ite (measurableSet_cubeSet R |>.diff (measurableSet_openCubeSet R))
        measurable_const measurable_const
    have heq : (fun x i j => if x ∈ C then aExt x i j else 0) =
        (fun x i j => (if x ∈ U then aN x i j else 0) +
          (if x ∈ Set.diff C U then (1 : Mat 2) i j else 0)) := by
      funext x i j
      by_cases hxU : x ∈ U
      · have hxC : x ∈ C := openCubeSet_subset_cubeSet R hxU
        have hnotdiff : x ∉ Set.diff C U := by
          intro hd
          exact hd.2 hxU
        simp [aExt, hxU, hxC, hnotdiff]
      · by_cases hxC : x ∈ C
        · have hdiff : x ∈ Set.diff C U := ⟨hxC, hxU⟩
          simp [aExt, hxU, hxC, hdiff]
        · have hnotdiff : x ∉ Set.diff C U := by
            intro hd
            exact hxC hd.1
          simp [aExt, hxU, hxC, hnotdiff]
    rw [heq]
    exact hfirst.add hsecond
  have hEllExt : IsEllipticFieldOn 1 Θ C aExt := by
    refine ⟨hmeasExt, ?_⟩
    intro x hxC
    by_cases hxU : x ∈ U
    · simpa [aExt, hxU] using hEllN.2 x hxU
    · rw [show aExt x = 1 by simp [aExt, hxU]]
      exact Homogenization.isEllipticMatrix_one_one hΘ
  let aUn : CoeffField 2 := lam • aExt
  have hEllUn : IsEllipticFieldOn lam Lam C aUn := by
    have h := ASDExplicitGamma.Cold.cold_isEllipticFieldOn_smul hlam hEllExt
    have hLamEq : lam * (Lam * lam⁻¹) = Lam := by field_simp [hlam.ne']
    simpa [aUn, Θ, div_eq_mul_inv, hLamEq] using h
  have hnotBoundary : ∀ᵐ x ∂volume, x ∉ cubeBoundary R := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using volume_cubeBoundary_eq_zero R
  have hAE : aUn =ᵐ[volume.restrict C] a := by
    apply (ae_restrict_iff' (measurableSet_cubeSet R)).2
    filter_upwards [hnotBoundary] with x hnb hxC
    have hxU : x ∈ U := by
      by_contra hxu
      exact hnb (mem_cubeBoundary_iff.mpr ⟨hxC, hxu⟩)
    have hExt : aExt x = aN x := by simp [aExt, hxU]
    have hscale : lam • aN x = a x := by
      ext i j
      simp [aN, Pi.smul_apply, hlam.ne']
    change (lam • aExt) x = a x
    rw [Pi.smul_apply, hExt, hscale]
  have hCoarse : coarseBlockMatrix C aUn = coarseBlockMatrix U a := by
    calc
      coarseBlockMatrix C aUn = coarseBlockMatrix C a :=
        coarseBlockMatrix_congr_of_ae_eq hAE
      _ = coarseBlockMatrix U a :=
        coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R a
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.2 hlam
  have hs2 : (Real.sqrt lam) ^ 2 = lam := Real.sq_sqrt hlam.le
  have hRescale : coarseBlockMatrix C aUn =
      coarseMatrixRescale (Real.sqrt lam) (coarseBlockMatrix C aExt) := by
    have hcoef : aUn = (Real.sqrt lam) ^ 2 • aExt := by
      ext x i j
      simp [aUn, Pi.smul_apply, hs2]
    rw [hcoef]
    exact coarseBlockMatrix_sq_smul_triCube hEllExt hs
  have hdiagTop (i : Fin 2) :
      (coarseBlockMatrix C aExt).upperLeft i i ≤ 2 * Θ := by
    have h := old_signed_coarse_quadratic_cube_upper hEllExt
      (Pi.single i (1 : ℝ), 0)
    fin_cases i <;>
      simpa [blockVecDot, blockMatVecMul, vecDot, matVecMul, vecNormSq,
        Fin.sum_univ_two, Pi.single_apply] using h
  have hdiagBottom (i : Fin 2) :
      (coarseBlockMatrix C aExt).lowerRight i i ≤ 2 := by
    have h := old_signed_coarse_quadratic_cube_upper hEllExt
      (0, Pi.single i (1 : ℝ))
    fin_cases i <;>
      simpa [blockVecDot, blockMatVecMul, vecDot, matVecMul, vecNormSq,
        Fin.sum_univ_two, Pi.single_apply] using h
  have htraceTop : Matrix.trace (coarseBlockMatrix C aExt).upperLeft ≤ 4 * Θ := by
    calc
      Matrix.trace (coarseBlockMatrix C aExt).upperLeft =
          (coarseBlockMatrix C aExt).upperLeft 0 0 +
            (coarseBlockMatrix C aExt).upperLeft 1 1 := by
        simp [Matrix.trace, Fin.sum_univ_two]
      _ ≤ 2 * Θ + 2 * Θ := add_le_add (hdiagTop 0) (hdiagTop 1)
      _ = 4 * Θ := by ring
  have htraceBottom : Matrix.trace (coarseBlockMatrix C aExt).lowerRight ≤ 4 := by
    calc
      Matrix.trace (coarseBlockMatrix C aExt).lowerRight =
          (coarseBlockMatrix C aExt).lowerRight 0 0 +
            (coarseBlockMatrix C aExt).lowerRight 1 1 := by
        simp [Matrix.trace, Fin.sum_univ_two]
      _ ≤ 2 + 2 := add_le_add (hdiagBottom 0) (hdiagBottom 1)
      _ = 4 := by norm_num
  have hTraceEq : traceDefect U a 1 = traceDefect C aUn 1 := by
    unfold traceDefect
    rw [← hCoarse]
  have hTraceFormula : traceDefect C aUn 1 =
      lam * Matrix.trace (coarseBlockMatrix C aExt).upperLeft +
        lam⁻¹ * Matrix.trace (coarseBlockMatrix C aExt).lowerRight - 4 := by
    unfold traceDefect
    rw [hRescale]
    simp only [coarseMatrixRescale, inv_one, one_mul, Matrix.trace_smul, smul_eq_mul]
    have hInv : (Real.sqrt lam) ^ (-2 : ℤ) = lam⁻¹ := by
      rw [zpow_neg, zpow_ofNat, hs2]
    rw [hs2, hInv]
  have hNonneg : 0 ≤ traceDefect C aUn 1 :=
    traceDefect_nonneg_of_ellipticFieldOn_triCube hlam hEllUn one_pos
  have hUpper : traceDefect C aUn 1 ≤ 4 * (Lam + lam⁻¹) := by
    rw [hTraceFormula]
    have h1 := mul_le_mul_of_nonneg_left htraceTop hlam.le
    have h2 := mul_le_mul_of_nonneg_left htraceBottom (inv_nonneg.mpr hlam.le)
    have hLamEq : lam * Θ = Lam := by
      dsimp [Θ]
      field_simp [hlam.ne']
    nlinarith [h1, h2, hLamEq]
  rw [hTraceEq]
  exact ⟨hNonneg, hUpper⟩

private theorem old_signed_trace_average_bounds (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (j : ℕ) :
    0 ≤ descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) ∧
      descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) ≤
        4 * (Lam + lam⁻¹) := by
  let C : ℝ := 4 * (Lam + lam⁻¹)
  have hpoint (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
      0 ≤ traceDefect (openCubeSet R) a 1 ∧ traceDefect (openCubeSet R) a 1 ≤ C := by
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    simpa [C] using old_signed_trace_defect_open_bounds Q R hsub hEll
  constructor
  · exact descendantsAverage_nonneg Q j _ (fun R hR => (hpoint R hR).1)
  · have havg := descendantsAverage_le_descendantsAverage Q j
      (fun R hR => (hpoint R hR).2)
    simpa only [descendantsAverage_const] using havg

/-- The actual OLD trace history also has a convergent real depth series, for
consumers that convert the complete ENNReal sum to `toReal`. -/
theorem old_signed_trace_depth_series_summable (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1)) := by
  have hlam : 0 < lam := (hEll.2 (cubeCenter Q) (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q))).1
  have hLam : lam ≤ Lam := (hEll.2 (cubeCenter Q) (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q))).2.1
  have hLamPos : 0 < Lam := lt_of_lt_of_le hlam hLam
  have hαpos : 0 < Scalar.inverseHistoryDiscount := Scalar.inverse_history_discount_range.1
  have hαlt : Scalar.inverseHistoryDiscount < 1 := Scalar.inverse_history_discount_range.2
  have hα : 0 ≤ Scalar.inverseHistoryDiscount := hαpos.le
  let C : ℝ := 4 * (Lam + lam⁻¹)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgeom : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j * C) :=
    (summable_geometric_of_lt_one hα hαlt).mul_right C
  apply Summable.of_nonneg_of_le
  · intro j
    exact mul_nonneg (pow_nonneg hα j) (old_signed_trace_average_bounds Q a hEll j).1
  · intro j
    exact mul_le_mul_of_nonneg_left (old_signed_trace_average_bounds Q a hEll j).2
      (pow_nonneg hα j)
  · exact hgeom

private theorem old_signed_response_depth_max_le (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (j : ℕ) :
    Scalar.fullResponseDepthMax Q a j ≤ 2 * (Lam + lam⁻¹) := by
  unfold Scalar.fullResponseDepthMax
  apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q j)
  intro R hR
  have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hEllR := hEll.mono (measurableSet_openCubeSet R) hsub
  have hnorm := old_signed_coarse_operator_norm_open_le R hEllR
  simpa only [Scalar.fullResponseOperatorNorm,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube] using hnorm

/-- The actual OLD full-response maxima have a convergent real depth series. -/
theorem old_signed_response_depth_series_summable (Q : TriadicCube 2) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j *
      Scalar.fullResponseDepthMax Q a j) := by
  have hlam : 0 < lam := (hEll.2 (cubeCenter Q) (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q))).1
  have hLam : lam ≤ Lam := (hEll.2 (cubeCenter Q) (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos Q))).2.1
  have hLamPos : 0 < Lam := lt_of_lt_of_le hlam hLam
  have hαpos : 0 < Scalar.inverseHistoryDiscount := Scalar.inverse_history_discount_range.1
  have hαlt : Scalar.inverseHistoryDiscount < 1 := Scalar.inverse_history_discount_range.2
  have hα : 0 ≤ Scalar.inverseHistoryDiscount := hαpos.le
  let C : ℝ := 2 * (Lam + lam⁻¹)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgeom : Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ j * C) :=
    (summable_geometric_of_lt_one hα hαlt).mul_right C
  apply Summable.of_nonneg_of_le
  · intro j
    exact mul_nonneg (pow_nonneg hα j)
      (Scalar.full_response_depth_max_nonneg Q a j)
  · intro j
    exact mul_le_mul_of_nonneg_left (old_signed_response_depth_max_le Q a hEll j)
      (pow_nonneg hα j)
  · exact hgeom

end

end ASDExplicitGamma.Native
