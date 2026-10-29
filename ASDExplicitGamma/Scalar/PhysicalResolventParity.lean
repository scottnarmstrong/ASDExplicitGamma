module

public import ASDExplicitGamma.Scalar.PhysicalResolventIdentity
public import ASDExplicitGamma.Scalar.ResolventParityHilbert
public import ASDExplicitGamma.Scalar.ResolventGaussianParity
public import ASDExplicitGamma.Gaussian.ModelMoments
public import ASDExplicitGamma.Inverse.BankLocal
public import Mathlib.Tactic.NoncommRing

/-! The parity reduction for the actual OLD coefficient and fresh q3 shell. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Response
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped InnerProduct InnerProductSpace Topology ENNReal

noncomputable section

local instance physicalParityFiniteMeasure (Q : TriadicCube 2) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

variable {Y X : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

theorem pureFluxBlockInserted_opNorm_le (D : X →L[ℝ] Y) :
    ‖pureFluxBlockOperator 0 D‖ ≤ ‖D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
  intro z
  have hz : ‖z‖ ^ 2 = ‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
  have hD : ‖D.adjoint‖ = ‖D‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
  have hpair := pureFluxBlockOperator_apply 0 D z
  have hfst : (pureFluxBlockOperator 0 D z).fst = D z.snd := by
    change (pureFluxBlockOperator 0 D z).ofLp.1 = D z.snd
    rw [hpair]
    simp [WithLp.ofLp_snd]
  have hsnd : (pureFluxBlockOperator 0 D z).snd = -(D.adjoint z.fst) := by
    change (pureFluxBlockOperator 0 D z).ofLp.2 = -(D.adjoint z.fst)
    rw [hpair]
    simp [WithLp.ofLp_fst]
  have hTnorm : ‖pureFluxBlockOperator 0 D z‖ ^ 2 =
      ‖D z.snd‖ ^ 2 + ‖D.adjoint z.fst‖ ^ 2 := by
    calc
      _ = ‖(pureFluxBlockOperator 0 D z).fst‖ ^ 2 +
          ‖(pureFluxBlockOperator 0 D z).snd‖ ^ 2 :=
        WithLp.prod_norm_sq_eq_of_L2 _
      _ = _ := by rw [hfst, hsnd, norm_neg]
  have hfirst : ‖D z.snd‖ ≤ ‖D‖ * ‖z.snd‖ := D.le_opNorm z.snd
  have hsecond : ‖D.adjoint z.fst‖ ≤ ‖D‖ * ‖z.fst‖ := by
    calc
      ‖D.adjoint z.fst‖ ≤ ‖D.adjoint‖ * ‖z.fst‖ := D.adjoint.le_opNorm _
      _ = ‖D‖ * ‖z.fst‖ := by rw [hD]
  have hfirstSq : ‖D z.snd‖ ^ 2 ≤ (‖D‖ * ‖z.snd‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hfirst
  have hsecondSq : ‖D.adjoint z.fst‖ ^ 2 ≤ (‖D‖ * ‖z.fst‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hsecond
  have hsquare : ‖pureFluxBlockOperator 0 D z‖ ^ 2 ≤ (‖D‖ * ‖z‖) ^ 2 := by
    rw [hTnorm]
    calc
      _ ≤ (‖D‖ * ‖z.snd‖) ^ 2 + (‖D‖ * ‖z.fst‖) ^ 2 :=
        add_le_add hfirstSq hsecondSq
      _ = ‖D‖ ^ 2 * (‖z.fst‖ ^ 2 + ‖z.snd‖ ^ 2) := by ring
      _ = ‖D‖ ^ 2 * ‖z‖ ^ 2 := by rw [← hz]
      _ = (‖D‖ * ‖z‖) ^ 2 := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).1 hsquare

private theorem pureFluxBlockBilinear_alpha_coercive {α : ℝ} (hα : 0 < α)
    (A : X →L[ℝ] Y) (z : pureFluxPair (Y := Y) (X := X)) :
    α * ‖z‖ ^ 2 ≤ pureFluxBlockBilinear α A z z := by
  rw [pureFluxBlockBilinear_apply, WithLp.prod_inner_apply,
    pureFluxBlockOperator_apply]
  let zy : Y := z.fst
  let zx : X := z.snd
  have hadj := ContinuousLinearMap.adjoint_inner_left A zx zy
  have hcross : ⟪A zx, zy⟫_ℝ = ⟪A.adjoint zy, zx⟫_ℝ := by
    calc
      ⟪A zx, zy⟫_ℝ = ⟪zy, A zx⟫_ℝ := real_inner_comm _ _
      _ = ⟪A.adjoint zy, zx⟫_ℝ := hadj.symm
  have hnorm : ‖z‖ ^ 2 = ‖zy‖ ^ 2 + ‖zx‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.ofLp_fst, WithLp.ofLp_snd]
  simp only [inner_add_left, inner_smul_left, inner_neg_left,
    starRingEnd_apply, star_trivial]
  rw [hcross]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  nlinarith [hnorm]

theorem pureFluxBlockInverse_opNorm_le {α : ℝ} (hα : 0 < α)
    (A : X →L[ℝ] Y) :
    ‖pureFluxBlockInverse α hα A‖ ≤ α⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hα.le)
  intro f
  let B := pureFluxBlockInverse α hα A
  let T := pureFluxBlockOperator α A
  let z := B f
  have hsys : T z = f := by
    have h := congrArg (fun L : _ →L[ℝ] _ => L f)
      (pureFluxBlockInverse_left α hα A)
    simpa [B, T, z, ContinuousLinearMap.mul_def] using h
  have hbound : α * ‖z‖ ^ 2 ≤
      pureFluxBlockBilinear α A z z := by
    exact pureFluxBlockBilinear_alpha_coercive hα A z
  rw [pureFluxBlockBilinear_apply, hsys] at hbound
  have hinner : ⟪f, z⟫_ℝ ≤ ‖f‖ * ‖z‖ :=
    (le_abs_self _).trans (abs_real_inner_le_norm f z)
  have hmul : α * ‖z‖ ≤ ‖f‖ := by
    by_contra hn
    have hlt : ‖f‖ < α * ‖z‖ := lt_of_not_ge hn
    have hzpos : 0 < ‖z‖ := by
      by_contra hznot
      have hzle : ‖z‖ ≤ 0 := le_of_not_gt hznot
      have hz0 : ‖z‖ = 0 := le_antisymm hzle (norm_nonneg _)
      rw [hz0] at hlt
      simp at hlt
      exact (not_lt_of_ge (norm_nonneg f)) hlt
    have hmul' := mul_lt_mul_of_pos_right hlt hzpos
    nlinarith [hbound, hinner]
  have hnorm : ‖z‖ ≤ ‖f‖ / α := (le_div_iff₀ hα).2 (by nlinarith [hmul])
  calc
    ‖pureFluxBlockInverse α hα A f‖ = ‖z‖ := rfl
    _ ≤ ‖f‖ / α := hnorm
    _ = α⁻¹ * ‖f‖ := by field_simp

private theorem pureFluxBlockOperator_sub_eq_inserted {α : ℝ}
    (A A' : X →L[ℝ] Y) :
    pureFluxBlockOperator α A' - pureFluxBlockOperator α A =
      pureFluxBlockOperator 0 (A' - A) := by
  have hA : A' = A + (A' - A) := by abel
  have hM : pureFluxBlockOperator α A' =
      pureFluxBlockOperator α A + pureFluxBlockOperator 0 (A' - A) := by
    exact (congrArg (pureFluxBlockOperator α) hA).trans
      (pureFluxBlockOperator_add α A (A' - A)).symm
  rw [hM]
  abel

private theorem pureFluxBlockInserted_continuous :
    Continuous (fun D : X →L[ℝ] Y => pureFluxBlockOperator 0 D) := by
  let c : NNReal := 1
  have hc : (c : ℝ) = 1 := rfl
  have hLip : LipschitzWith c
      (fun D : X →L[ℝ] Y => pureFluxBlockOperator 0 D) := by
    apply LipschitzWith.of_dist_le_mul
    intro D D'
    rw [dist_eq_norm, dist_eq_norm]
    have h := pureFluxBlockInserted_opNorm_le (D - D')
    rw [pureFluxBlockOperator_sub_eq_inserted]
    simpa only [hc, one_mul] using h
  exact hLip.continuous

private theorem pureFluxBlockInverse_resolvent_identity {α : ℝ}
    (hα : 0 < α) (A A' : X →L[ℝ] Y) :
    pureFluxBlockInverse α hα A - pureFluxBlockInverse α hα A' =
      pureFluxBlockInverse α hα A *
        (pureFluxBlockOperator α A' - pureFluxBlockOperator α A) *
          pureFluxBlockInverse α hα A' := by
  let B := pureFluxBlockInverse α hα A
  let B' := pureFluxBlockInverse α hα A'
  let T := pureFluxBlockOperator α A
  let T' := pureFluxBlockOperator α A'
  have hBT : B * T = 1 := pureFluxBlockInverse_right α hα A
  have hT'B' : T' * B' = 1 := pureFluxBlockInverse_left α hα A'
  change B - B' = B * (T' - T) * B'
  calc
    B - B' = B * 1 - 1 * B' := by simp
    _ = B * (T' * B') - (B * T) * B' := by rw [hT'B', hBT]
    _ = (B * T') * B' - (B * T) * B' := by rw [← mul_assoc]
    _ = (B * T' - B * T) * B' := by rw [sub_mul]
    _ = B * (T' - T) * B' := by rw [← mul_sub]

private theorem pureFluxBlockInverse_difference_norm_le {α : ℝ}
    (hα : 0 < α) (A A' : X →L[ℝ] Y) :
    ‖pureFluxBlockInverse α hα A - pureFluxBlockInverse α hα A'‖ ≤
      (α⁻¹) ^ 2 * ‖A - A'‖ := by
  rw [pureFluxBlockInverse_resolvent_identity hα A A',
    pureFluxBlockOperator_sub_eq_inserted]
  have hB := pureFluxBlockInverse_opNorm_le hα A
  have hB' := pureFluxBlockInverse_opNorm_le hα A'
  have hC := pureFluxBlockInserted_opNorm_le (A' - A)
  let B := pureFluxBlockInverse α hα A
  let C := pureFluxBlockOperator 0 (A' - A)
  let B' := pureFluxBlockInverse α hα A'
  have hBC : ‖B * C‖ ≤ ‖B‖ * ‖C‖ := norm_mul_le B C
  have hBCB : ‖B * C * B'‖ ≤ (‖B‖ * ‖C‖) * ‖B'‖ := by
    calc
      ‖B * C * B'‖ ≤ ‖B * C‖ * ‖B'‖ := norm_mul_le (B * C) B'
      _ ≤ (‖B‖ * ‖C‖) * ‖B'‖ :=
        mul_le_mul_of_nonneg_right hBC (norm_nonneg B')
  calc
    ‖B * C * B'‖ ≤ (‖B‖ * ‖C‖) * ‖B'‖ := hBCB
    _ ≤ (α⁻¹ * ‖A' - A‖) * α⁻¹ := by gcongr
    _ = (α⁻¹) ^ 2 * ‖A - A'‖ := by rw [norm_sub_rev]; ring

private theorem pureFluxBlockInverse_continuous {α : ℝ} (hα : 0 < α) :
    Continuous (fun A : X →L[ℝ] Y => pureFluxBlockInverse α hα A) := by
  let c : NNReal := ⟨(α⁻¹) ^ 2, sq_nonneg _⟩
  have hc : (c : ℝ) = (α⁻¹) ^ 2 := rfl
  have hLip : LipschitzWith c
      (fun A : X →L[ℝ] Y => pureFluxBlockInverse α hα A) := by
    apply LipschitzWith.of_dist_le_mul
    intro A A'
    rw [dist_eq_norm, dist_eq_norm]
    simpa only [hc] using pureFluxBlockInverse_difference_norm_le hα A A'
  exact hLip.continuous

private theorem real_inner_norm_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x y : H) :
    ‖⟪x, y⟫_ℝ‖ ≤ ‖x‖ * ‖y‖ := by
  rw [Real.norm_eq_abs]
  exact abs_real_inner_le_norm x y

private theorem hilbertG1LinearTerm_norm_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B J C : H →L[ℝ] H) (f : H) :
    ‖hilbertG1LinearTerm B J f C‖ ≤ ‖J (B f)‖ * ‖C (B f)‖ := by
  unfold hilbertG1LinearTerm
  rw [norm_neg]
  exact real_inner_norm_le _ _

private theorem hilbertG1HessianTerm_norm_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B J C : H →L[ℝ] H) (f : H) :
    ‖hilbertG1HessianTerm B J f C‖ ≤
      ‖J (B f)‖ * ‖(C * B * C) (B f)‖ := by
  unfold hilbertG1HessianTerm
  exact real_inner_norm_le _ _

private theorem hilbertG1CubicTerm_norm_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B J C : H →L[ℝ] H) (f : H) :
    ‖hilbertG1CubicTerm B J f C‖ ≤
      ‖J (B f)‖ * ‖(C * B * C * B * C) (B f)‖ := by
  unfold hilbertG1CubicTerm
  rw [norm_neg]
  exact real_inner_norm_le _ _

private theorem hilbertG1QuarticTerm_norm_le {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B J C N : H →L[ℝ] H) (f : H) :
    ‖hilbertG1QuarticTerm B J f C N‖ ≤
      ‖J ((C * B * C) (B f))‖ *
        ‖N ((C * B * C) (B f))‖ := by
  unfold hilbertG1QuarticTerm
  exact real_inner_norm_le _ _

private theorem physicalProjectedCoefficient_continuous (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun k : ResponseCoefficient (openCubeSet Q) =>
      physicalProjectedCoefficient Q σ hσ k) := by
  have hS : Continuous (fun k : ResponseCoefficient (openCubeSet Q) =>
      responseShearL2Operator σ hσ k) :=
    (responseShearL2Family (measurableSet_openCubeSet Q) σ hσ).continuous
  fun_prop [physicalProjectedCoefficient, physicalPositiveShear,
    responseShearL2Operator]

private theorem physicalProjectedCoefficient_neg (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient (openCubeSet Q)) :
    physicalProjectedCoefficient Q σ hσ (-H) =
      -physicalProjectedCoefficient Q σ hσ H := by
  have hzero : physicalProjectedCoefficient Q σ hσ (0 : ResponseCoefficient
      (openCubeSet Q)) = 0 := by
    have hS : responseShearL2Operator σ hσ (0 : ResponseCoefficient
        (openCubeSet Q)) = 0 :=
      map_zero (responseShearL2FamilyLinear
        (measurableSet_openCubeSet Q) σ hσ)
    simp [physicalProjectedCoefficient, physicalPositiveShear, hS]
  have hadd := physicalProjectedCoefficient_add Q σ hσ (-H) H
  rw [neg_add_cancel, hzero] at hadd
  have hadd' : physicalProjectedCoefficient Q σ hσ (-H) +
      physicalProjectedCoefficient Q σ hσ H = 0 := by
    simpa [physicalProjectedInsertion] using hadd.symm
  calc
    physicalProjectedCoefficient Q σ hσ (-H) =
        physicalProjectedCoefficient Q σ hσ (-H) +
          physicalProjectedCoefficient Q σ hσ H -
            physicalProjectedCoefficient Q σ hσ H := by abel
    _ = 0 - physicalProjectedCoefficient Q σ hσ H := by rw [hadd']
    _ = -physicalProjectedCoefficient Q σ hσ H := by abel

private theorem physicalProjectedCoefficient_opNorm_le (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ) (H : ResponseCoefficient (openCubeSet Q)) :
    ‖physicalProjectedCoefficient Q σ hσ H‖ ≤ ‖H‖ / σ := by
  let U := openCubeSet Q
  let first := hilbertPureFirstL2 U
  let second := hilbertSecondProjection U
  let flux := (physicalFluxSpace Q).toSubmodule
  let potential := (physicalPotentialSpace Q).toSubmodule
  have hfirst : ‖first‖ ≤ 1 := by
    dsimp [first, hilbertPureFirstL2]
    calc
      ‖pureFirst.toContinuousLinearMap.compLpL 2 (volumeMeasureOn U)‖ ≤
          ‖pureFirst.toContinuousLinearMap‖ :=
            ContinuousLinearMap.norm_compLpL_le _
      _ = 1 := by simp
  have hsecondVec : ‖hilbertBlockSecondProjectionVec‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simpa [hilbertBlockSecondProjectionVec] using PiLp.norm_apply_le z 1
  have hsecond : ‖second‖ ≤ 1 := by
    dsimp [second, hilbertSecondProjection]
    calc
      ‖hilbertBlockSecondProjectionVec.compLpL 2 (volumeMeasureOn U)‖ ≤
          ‖hilbertBlockSecondProjectionVec‖ :=
            ContinuousLinearMap.norm_compLpL_le _
      _ ≤ 1 := hsecondVec
  have hfluxProj : ‖flux.orthogonalProjectionOnto‖ ≤ 1 :=
    flux.orthogonalProjectionOnto_norm_le
  have hfluxSub : ‖flux.subtypeL‖ ≤ 1 := flux.norm_subtypeL_le
  have hpotSub : ‖potential.subtypeL‖ ≤ 1 := potential.norm_subtypeL_le
  have hshear : ‖responseShearL2Operator σ hσ H‖ ≤ ‖H‖ / σ :=
    responseShearL2Operator_opNorm_le σ hσ H
  have hpositive : ‖physicalPositiveShear Q σ hσ H‖ ≤ ‖H‖ / σ := by
    unfold physicalPositiveShear
    change ‖-(hilbertSecondProjection U).comp
      ((responseShearL2Operator σ hσ H).comp
        (hilbertPureFirstL2 U))‖ ≤ ‖H‖ / σ
    calc
      ‖-(second.comp ((responseShearL2Operator σ hσ H).comp first))‖ =
          ‖second.comp ((responseShearL2Operator σ hσ H).comp first)‖ := norm_neg _
      _ ≤ ‖second‖ * ‖(responseShearL2Operator σ hσ H).comp first‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖second‖ *
          (‖responseShearL2Operator σ hσ H‖ * ‖first‖) := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖H‖ / σ := by
        calc
          ‖second‖ *
              (‖responseShearL2Operator σ hσ H‖ * ‖first‖) ≤
            1 * ((‖H‖ / σ) * 1) := by
              gcongr
          _ = ‖H‖ / σ := by ring
  unfold physicalProjectedCoefficient
  change ‖(flux.subtypeL.comp flux.orthogonalProjectionOnto).comp
      ((physicalPositiveShear Q σ hσ H).comp potential.subtypeL)‖ ≤ ‖H‖ / σ
  calc
    ‖(flux.subtypeL.comp flux.orthogonalProjectionOnto).comp
        ((physicalPositiveShear Q σ hσ H).comp potential.subtypeL)‖ ≤
      ‖(flux.subtypeL.comp flux.orthogonalProjectionOnto)‖ *
        ‖(physicalPositiveShear Q σ hσ H).comp potential.subtypeL‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖flux.subtypeL‖ * ‖flux.orthogonalProjectionOnto‖) *
        (‖physicalPositiveShear Q σ hσ H‖ * ‖potential.subtypeL‖) := by
          gcongr <;> exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖H‖ / σ := by
      calc
        (‖flux.subtypeL‖ * ‖flux.orthogonalProjectionOnto‖) *
            (‖physicalPositiveShear Q σ hσ H‖ * ‖potential.subtypeL‖) ≤
          (1 * 1) * ((‖H‖ / σ) * 1) := by gcongr
        _ = ‖H‖ / σ := by ring

private theorem physicalBlock_parityAdjoint {Y X : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (α : ℝ) (A : X →L[ℝ] Y) :
    (pureFluxBlockOperator α A).adjoint *
        pureFluxParity (Y := Y) (X := X) =
      pureFluxParity (Y := Y) (X := X) *
        pureFluxBlockOperator α A := by
  apply ContinuousLinearMap.ext
  intro z
  apply ext_inner_right ℝ
  intro w
  change ⟪(pureFluxBlockOperator α A).adjoint
      (pureFluxParity z), w⟫_ℝ =
    ⟪pureFluxParity (pureFluxBlockOperator α A z), w⟫_ℝ
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [WithLp.prod_inner_apply, WithLp.prod_inner_apply,
    pureFluxParity_apply, pureFluxBlockOperator_apply,
    pureFluxParity_apply, pureFluxBlockOperator_apply]
  have hadj₁ : ⟪z.ofLp.1, A w.ofLp.2⟫_ℝ =
      ⟪A.adjoint z.ofLp.1, w.ofLp.2⟫_ℝ :=
    (ContinuousLinearMap.adjoint_inner_left A w.ofLp.2 z.ofLp.1).symm
  have hadj₂ : ⟪z.ofLp.2, A.adjoint w.ofLp.1⟫_ℝ =
      ⟪A z.ofLp.2, w.ofLp.1⟫_ℝ := by
    calc
      ⟪z.ofLp.2, A.adjoint w.ofLp.1⟫_ℝ =
          ⟪A.adjoint w.ofLp.1, z.ofLp.2⟫_ℝ := real_inner_comm _ _
      _ = ⟪w.ofLp.1, A z.ofLp.2⟫_ℝ :=
        ContinuousLinearMap.adjoint_inner_left A z.ofLp.2 w.ofLp.1
      _ = ⟪A z.ofLp.2, w.ofLp.1⟫_ℝ := real_inner_comm _ _
  simp only [inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, inner_neg_left, inner_neg_right,
    starRingEnd_apply, star_trivial]
  simp only [neg_neg, mul_neg, neg_add]
  rw [hadj₁, hadj₂]
  ring

abbrev physicalParityHilbert (Q : TriadicCube 2) :=
  pureFluxPair (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule)

noncomputable def physicalParityCoefficient
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q))
    (x : C(K, ℝ)) :
    (physicalPotentialSpace Q).toSubmodule →L[ℝ]
      HilbertVectorL2 (openCubeSet Q) :=
  physicalProjectedCoefficient Q σ hσ (R x)

noncomputable def physicalParityOldBlock
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (ν σ : ℝ) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q))
    (x : C(K, ℝ)) :
    physicalParityHilbert Q →L[ℝ] physicalParityHilbert Q :=
  pureFluxBlockOperator (ν / σ)
    (physicalParityCoefficient Q σ hσ R x)

noncomputable def physicalParityOldInverse
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q))
    (x : C(K, ℝ)) :
    physicalParityHilbert Q →L[ℝ] physicalParityHilbert Q :=
  pureFluxBlockInverse (ν / σ) (div_pos hν hσ)
    (physicalParityCoefficient Q σ hσ R x)

noncomputable def physicalParityInsertionBlock
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q))
    (y : C(K, ℝ)) :
    physicalParityHilbert Q →L[ℝ] physicalParityHilbert Q :=
  pureFluxBlockOperator 0 (physicalParityCoefficient Q σ hσ R y)

noncomputable def physicalParityNewInverse
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q))
    (x y : C(K, ℝ)) :
    physicalParityHilbert Q →L[ℝ] physicalParityHilbert Q :=
  pureFluxBlockInverse (ν / σ) (div_pos hν hσ)
    (physicalParityCoefficient Q σ hσ R x +
      physicalParityCoefficient Q σ hσ R y)

private theorem pureFluxBlockOperator_inserted_neg {Y X : Type*}
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (D : X →L[ℝ] Y) :
    pureFluxBlockOperator 0 (-D) = -pureFluxBlockOperator 0 D := by
  ext z
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ Y X).injective
  change (pureFluxBlockOperator 0 (-D) z).ofLp =
    (-pureFluxBlockOperator 0 D z).ofLp
  simp [pureFluxBlockOperator_apply]

/-- The linear term of the physical four-term response identity, as a function
of the completed OLD coefficient and the inserted fresh coefficient. -/
noncomputable def physicalParityLinearObservable
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    C(K, ℝ) × C(K, ℝ) → ℝ := fun p =>
  let A := physicalParityCoefficient Q σ hσ R
  let B := pureFluxBlockInverse (ν / σ) (div_pos hν hσ) (A p.1)
  let C := pureFluxBlockOperator 0 (A p.2)
  let J := pureFluxParity (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule)
  let f : physicalParityHilbert Q :=
    pureFluxLoad (Y := HilbertVectorL2 (openCubeSet Q))
      (X := (physicalPotentialSpace Q).toSubmodule)
      (physicalConstantLoad Q e)
  hilbertG1LinearTerm B J f C

/-- The OLD-law Hessian term in the physical four-term response identity. -/
noncomputable def physicalParityHessianObservable
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    C(K, ℝ) × C(K, ℝ) → ℝ := fun p =>
  let A := physicalParityCoefficient Q σ hσ R
  let B := pureFluxBlockInverse (ν / σ) (div_pos hν hσ) (A p.1)
  let C := pureFluxBlockOperator 0 (A p.2)
  let J := pureFluxParity (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule)
  let f : physicalParityHilbert Q :=
    pureFluxLoad (Y := HilbertVectorL2 (openCubeSet Q))
      (X := (physicalPotentialSpace Q).toSubmodule)
      (physicalConstantLoad Q e)
  hilbertG1HessianTerm B J f C

/-- The cubic term in the physical four-term response identity. -/
noncomputable def physicalParityCubicObservable
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    C(K, ℝ) × C(K, ℝ) → ℝ := fun p =>
  let A := physicalParityCoefficient Q σ hσ R
  let B := pureFluxBlockInverse (ν / σ) (div_pos hν hσ) (A p.1)
  let C := pureFluxBlockOperator 0 (A p.2)
  let J := pureFluxParity (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule)
  let f : physicalParityHilbert Q :=
    pureFluxLoad (Y := HilbertVectorL2 (openCubeSet Q))
      (X := (physicalPotentialSpace Q).toSubmodule)
      (physicalConstantLoad Q e)
  hilbertG1CubicTerm B J f C

/-- The actual NEW-resolvent quartic term in the physical response identity. -/
noncomputable def physicalParityQuarticObservable
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    C(K, ℝ) × C(K, ℝ) → ℝ := fun p =>
  let A := physicalParityCoefficient Q σ hσ R
  let B := pureFluxBlockInverse (ν / σ) (div_pos hν hσ) (A p.1)
  let C := pureFluxBlockOperator 0 (A p.2)
  let N := pureFluxBlockInverse (ν / σ) (div_pos hν hσ)
    (A p.1 + A p.2)
  let J := pureFluxParity (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule)
  let f : physicalParityHilbert Q :=
    pureFluxLoad (Y := HilbertVectorL2 (openCubeSet Q))
      (X := (physicalPotentialSpace Q).toSubmodule)
      (physicalConstantLoad Q e)
  hilbertG1QuarticTerm B J f C N

/-- The physical response increment from the OLD coefficient to its actual
fresh-shell update. -/
noncomputable def physicalParityResponseIncrement
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    C(K, ℝ) × C(K, ℝ) → ℝ := fun p =>
  let hvol : 0 < (MeasureTheory.volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  responseFrameEnergyObservable (measurableSet_openCubeSet Q) hvol
      ν σ hν hσ (0, e) (R (p.1 + p.2)) -
    responseFrameEnergyObservable (measurableSet_openCubeSet Q) hvol
      ν σ hν hσ (0, e) (R p.1)

/-- The source's next scalar shell restricted to the compact region. -/
def physicalParityFreshField {K : Set (Vec 2)} [CompactSpace K]
    (m : ℤ) : Cutoff.CutoffSample 2 → C(K, ℝ) := fun ω =>
  shellFieldScalarRestriction K (ω.1 (m + 1))

/-- The actual OLD coefficient and next scalar shell in the cutoff coupling. -/
def physicalParityPairMap {K : Set (Vec 2)} [CompactSpace K]
    (m : ℤ) : Cutoff.CutoffSample 2 → C(K, ℝ) × C(K, ℝ) := fun ω =>
  (olderField K m ω, physicalParityFreshField (K := K) m ω)

/-- The OLD marginal of the actual cutoff sample law. -/
noncomputable def physicalParityOldMarginal
    {K : Set (Vec 2)} [CompactSpace K] (M : ABKModel 2) (m : ℤ) :
    Measure (C(K, ℝ)) :=
  (Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)

/-- The fresh-shell marginal of the actual cutoff sample law. -/
noncomputable def physicalParityFreshMarginal
    {K : Set (Vec 2)} [CompactSpace K] (M : ABKModel 2) (m : ℤ) :
    Measure (C(K, ℝ)) :=
  (Cutoff.cutoffSampleLaw M).toMeasure.map (physicalParityFreshField (K := K) m)

/-- The independent OLD/fresh product law identified from the cutoff coupling. -/
noncomputable def physicalParityProductLaw
    {K : Set (Vec 2)} [CompactSpace K] (M : ABKModel 2) (m : ℤ) :
    Measure (C(K, ℝ) × C(K, ℝ)) :=
  (physicalParityOldMarginal M m).prod
    (physicalParityFreshMarginal M m)

private theorem physicalParity_observables_continuous
    {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (hQ : closure (openCubeSet Q) ⊆ K)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (e : Vec 2) :
    Continuous (physicalParityLinearObservable Q ν σ hν hσ
      (physicalResponseRestriction Q hQ) e) ∧
    Continuous (physicalParityHessianObservable Q ν σ hν hσ
      (physicalResponseRestriction Q hQ) e) ∧
    Continuous (physicalParityCubicObservable Q ν σ hν hσ
      (physicalResponseRestriction Q hQ) e) ∧
    Continuous (physicalParityQuarticObservable Q ν σ hν hσ
      (physicalResponseRestriction Q hQ) e) ∧
    Continuous (physicalParityResponseIncrement Q ν σ hν hσ
      (physicalResponseRestriction Q hQ) e) := by
  let U := openCubeSet Q
  let R := physicalResponseRestriction Q hQ
  let A := physicalParityCoefficient Q σ hσ R
  let α := ν / σ
  let hα : 0 < α := div_pos hν hσ
  let B := physicalParityOldInverse Q ν σ hν hσ R
  let C := physicalParityInsertionBlock Q σ hσ R
  let N : C(K, ℝ) → C(K, ℝ) → physicalParityHilbert Q →L[ℝ]
      physicalParityHilbert Q := fun x y =>
    pureFluxBlockInverse α hα (A x + A y)
  let J := pureFluxParity (Y := HilbertVectorL2 U)
    (X := (physicalPotentialSpace Q).toSubmodule)
  let f : pureFluxPair (Y := HilbertVectorL2 U)
      (X := (physicalPotentialSpace Q).toSubmodule) :=
    pureFluxLoad (Y := HilbertVectorL2 U)
      (X := (physicalPotentialSpace Q).toSubmodule)
      (physicalConstantLoad Q e)
  let linear : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityLinearObservable Q ν σ hν hσ R e
  let hessian : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityHessianObservable Q ν σ hν hσ R e
  let cubic : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityCubicObservable Q ν σ hν hσ R e
  let quartic : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityQuarticObservable Q ν σ hν hσ R e
  let responseIncrement : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityResponseIncrement Q ν σ hν hσ R e
  let Acont : C(K, ℝ) → (physicalPotentialSpace Q).toSubmodule →L[ℝ]
      HilbertVectorL2 U := fun x => A x
  have hAcont : Continuous Acont := by
    change Continuous (fun x =>
      physicalProjectedCoefficient Q σ hσ (R x))
    exact (physicalProjectedCoefficient_continuous Q σ hσ).comp R.continuous
  have hAadd (x y : C(K, ℝ)) : Acont x + Acont y = Acont (x + y) := by
    change physicalProjectedCoefficient Q σ hσ (R x) +
        physicalProjectedCoefficient Q σ hσ (R y) =
      physicalProjectedCoefficient Q σ hσ (R (x + y))
    rw [R.map_add]
    simpa [physicalProjectedInsertion] using
      (physicalProjectedCoefficient_add Q σ hσ (R x) (R y)).symm
  have hAprod : Continuous (fun p : C(K, ℝ) × C(K, ℝ) => A p.1 + A p.2) := by
    have hEq : (fun p : C(K, ℝ) × C(K, ℝ) => A p.1 + A p.2) =
        fun p => A (p.1 + p.2) := by
      funext p
      exact hAadd p.1 p.2
    rw [hEq]
    exact hAcont.comp (continuous_fst.add continuous_snd)
  have hBcont : Continuous (fun x : C(K, ℝ) => B x) := by
    change Continuous (fun x =>
      pureFluxBlockInverse α hα (Acont x))
    exact (pureFluxBlockInverse_continuous hα).comp hAcont
  have hCcont : Continuous (fun y : C(K, ℝ) => C y) := by
    change Continuous (fun y =>
      pureFluxBlockOperator 0 (Acont y))
    exact (pureFluxBlockInserted_continuous).comp hAcont
  have hNcont : Continuous (fun p : C(K, ℝ) × C(K, ℝ) => N p.1 p.2) := by
    have hNcont' : Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
        pureFluxBlockInverse α hα (A p.1 + A p.2)) :=
      (pureFluxBlockInverse_continuous hα).comp hAprod
    exact hNcont'
  have hlinearCont : Continuous linear := by
    change Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
      hilbertG1LinearTerm (B p.1) J f (C p.2))
    fun_prop [hilbertG1LinearTerm]
  have hhessianCont : Continuous hessian := by
    change Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
      hilbertG1HessianTerm (B p.1) J f (C p.2))
    fun_prop [hilbertG1HessianTerm]
  have hcubicCont : Continuous cubic := by
    change Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
      hilbertG1CubicTerm (B p.1) J f (C p.2))
    fun_prop [hilbertG1CubicTerm]
  have hquarticCont : Continuous quartic := by
    change Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
      hilbertG1QuarticTerm (B p.1) J f (C p.2) (N p.1 p.2))
    fun_prop [hilbertG1QuarticTerm]
  have hRespObservable : Continuous
      (responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (by
          rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
          exact cubeVolume_pos Q)
        ν σ hν hσ (0, e)) :=
    (responseFrameEnergyObservable_contDiff
      (measurableSet_openCubeSet Q)
      (by
        rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
        exact cubeVolume_pos Q)
      ν σ hν hσ (0, e)).continuous
  have hrespCont : Continuous responseIncrement := by
    change Continuous (fun p : C(K, ℝ) × C(K, ℝ) =>
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (by
          rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
          exact cubeVolume_pos Q)
        ν σ hν hσ (0, e) (R (p.1 + p.2)) -
      responseFrameEnergyObservable (measurableSet_openCubeSet Q)
        (by
          rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
          exact cubeVolume_pos Q)
        ν σ hν hσ (0, e) (R p.1))
    exact (hRespObservable.comp (R.continuous.comp
      (continuous_fst.add continuous_snd))).sub
      (hRespObservable.comp (R.continuous.comp continuous_fst))
  exact ⟨hlinearCont, hhessianCont, hcubicCont, hquarticCont, hrespCont⟩

private theorem physicalParity_newInverse_two_sided
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q))
    (x y : C(K, ℝ)) :
    (physicalParityOldBlock Q ν σ hσ R x +
      physicalParityInsertionBlock Q σ hσ R y) *
        physicalParityNewInverse Q ν σ hν hσ R x y = 1 ∧
    physicalParityNewInverse Q ν σ hν hσ R x y *
      (physicalParityOldBlock Q ν σ hσ R x +
        physicalParityInsertionBlock Q σ hσ R y) = 1 := by
  let A := physicalParityCoefficient Q σ hσ R
  let α := ν / σ
  have hα : 0 < α := div_pos hν hσ
  have hAdd : pureFluxBlockOperator α (A x) +
      pureFluxBlockOperator 0 (A y) =
        pureFluxBlockOperator α (A x + A y) :=
    pureFluxBlockOperator_add α (A x) (A y)
  constructor
  · change (pureFluxBlockOperator α (A x) +
      pureFluxBlockOperator 0 (A y)) *
        pureFluxBlockInverse α hα (A x + A y) = 1
    rw [hAdd]
    exact pureFluxBlockInverse_left α hα (A x + A y)
  · change pureFluxBlockInverse α hα (A x + A y) *
      (pureFluxBlockOperator α (A x) +
        pureFluxBlockOperator 0 (A y)) = 1
    rw [hAdd]
    exact pureFluxBlockInverse_right α hα (A x + A y)

private theorem physicalParity_insertion_neg
    {K : Set (Vec 2)} [CompactSpace K] (Q : TriadicCube 2)
    (σ : ℝ) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q))
    (y : C(K, ℝ)) :
    physicalParityInsertionBlock Q σ hσ R (-y) =
      -physicalParityInsertionBlock Q σ hσ R y := by
  let A := physicalParityCoefficient Q σ hσ R
  have hAneg : A (-y) = -A y := by
    change physicalProjectedCoefficient Q σ hσ (R (-y)) =
      -physicalProjectedCoefficient Q σ hσ (R y)
    rw [map_neg]
    exact physicalProjectedCoefficient_neg Q σ hσ (R y)
  change pureFluxBlockOperator 0 (A (-y)) =
    -pureFluxBlockOperator 0 (A y)
  rw [hAneg]
  exact pureFluxBlockOperator_inserted_neg (A y)

private theorem physicalParity_fresh_fourth_integrable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    {K : Set (Vec 2)} [CompactSpace K] (m : ℤ) :
    Integrable (fun z : C(K, ℝ) => (1 + ‖z‖) ^ 4)
      (physicalParityFreshMarginal M m) := by
  obtain ⟨T, v, hv, hlaw⟩ :=
    freshShell_map_scalarRestriction_eq_gaussianSeries M h hM m (K := K)
  have hSeriesLp : MemLp (gaussianSeriesLimitE hv T) ((6 : ℕ) : ℝ≥0∞)
      standardGaussianInfinitePi := by
    convert memLp_gaussianSeriesLimitE hv T (p := (6 : ℝ)) (by norm_num) using 1;
    norm_num
  have hGaussianFourth : Integrable
      (fun z : C(K, ℝ) => (1 + ‖z‖) ^ 4)
      (standardGaussianInfinitePi.map (gaussianSeriesLimitE hv T)) := by
    apply (integrable_map_measure (by fun_prop)
      (stronglyMeasurable_gaussianSeriesLimitE hv T).measurable.aemeasurable).mpr
    change Integrable
      (fun ω : ℕ → ℝ => (1 + ‖gaussianSeriesLimitE hv T ω‖) ^ 4)
      standardGaussianInfinitePi
    exact integrable_one_add_norm_pow_of_memLp (d := 4) hSeriesLp
  have hMarginal : physicalParityFreshMarginal M m =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hv T) := by
    change (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 =>
        shellFieldScalarRestriction K (ω.1 (m + 1))) = _
    exact hlaw
  rw [hMarginal]
  exact hGaussianFourth

private theorem physicalParity_terms_integrable
    {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (hQ : closure (openCubeSet Q) ⊆ K)
    (M : ABKModel 2) (m : ℤ) (σ : ℝ) (hσ : 0 < σ) (e : Vec 2)
    (h : ℝ) (hM : PlanarQ3Gaussian M h) :
    Integrable (physicalParityLinearObservable Q M.nu σ M.nu_pos hσ
      (physicalResponseRestriction Q hQ) e) (physicalParityProductLaw M m) ∧
    Integrable (physicalParityHessianObservable Q M.nu σ M.nu_pos hσ
      (physicalResponseRestriction Q hQ) e) (physicalParityProductLaw M m) ∧
    Integrable (physicalParityCubicObservable Q M.nu σ M.nu_pos hσ
      (physicalResponseRestriction Q hQ) e) (physicalParityProductLaw M m) ∧
    Integrable (physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ
      (physicalResponseRestriction Q hQ) e) (physicalParityProductLaw M m) := by
  let R := physicalResponseRestriction Q hQ
  let μold : Measure (C(K, ℝ)) := physicalParityOldMarginal M m
  let μfresh : Measure (C(K, ℝ)) := physicalParityFreshMarginal M m
  let A := physicalParityCoefficient Q σ hσ R
  let α := M.nu / σ
  let hα : 0 < α := div_pos M.nu_pos hσ
  let β : ℝ := α⁻¹
  let B := physicalParityOldInverse Q M.nu σ M.nu_pos hσ R
  let C := physicalParityInsertionBlock Q σ hσ R
  let N : C(K, ℝ) → C(K, ℝ) → physicalParityHilbert Q →L[ℝ]
      physicalParityHilbert Q := fun x y =>
    pureFluxBlockInverse α hα (A x + A y)
  let J := pureFluxParity (Y := HilbertVectorL2 (openCubeSet Q))
    (X := (physicalPotentialSpace Q).toSubmodule)
  let f : physicalParityHilbert Q :=
    pureFluxLoad (Y := HilbertVectorL2 (openCubeSet Q))
      (X := (physicalPotentialSpace Q).toSubmodule)
      (physicalConstantLoad Q e)
  let linear := physicalParityLinearObservable Q M.nu σ M.nu_pos hσ R e
  let hessian := physicalParityHessianObservable Q M.nu σ M.nu_pos hσ R e
  let cubic := physicalParityCubicObservable Q M.nu σ M.nu_pos hσ R e
  let quartic := physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ R e
  change Integrable linear (μold.prod μfresh) ∧
    Integrable hessian (μold.prod μfresh) ∧
    Integrable cubic (μold.prod μfresh) ∧
    Integrable quartic (μold.prod μfresh)
  obtain ⟨hlinearCont, hhessianCont, hcubicCont, hquarticCont, _⟩ :=
    physicalParity_observables_continuous Q hQ M.nu σ M.nu_pos hσ e
  have hβ : 0 ≤ β := inv_nonneg.mpr hα.le
  have hRnorm (y : C(K, ℝ)) : ‖R y‖ ≤ ‖y‖ :=
    physicalResponseRestriction_norm_le Q hQ y
  have hAnorm (y : C(K, ℝ)) : ‖A y‖ ≤ ‖y‖ / σ := by
    exact (physicalProjectedCoefficient_opNorm_le Q σ hσ (R y)).trans
      (div_le_div_of_nonneg_right (hRnorm y) hσ.le)
  have hBop (x : C(K, ℝ)) : ‖B x‖ ≤ β :=
    pureFluxBlockInverse_opNorm_le hα (A x)
  have hCop (y : C(K, ℝ)) : ‖C y‖ ≤ ‖y‖ / σ := by
    exact (pureFluxBlockInserted_opNorm_le (A y)).trans (hAnorm y)
  have hNop (x y : C(K, ℝ)) : ‖N x y‖ ≤ β :=
    pureFluxBlockInverse_opNorm_le hα (A x + A y)
  have hFreshPoly : Integrable (fun z : C(K, ℝ) => (1 + ‖z‖) ^ 4) μfresh :=
    physicalParity_fresh_fourth_integrable M h hM (K := K) m
  haveI : IsFiniteMeasure μold := by
    change IsFiniteMeasure ((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m))
    infer_instance
  haveI : IsFiniteMeasure μfresh := by
    change IsFiniteMeasure ((Cutoff.cutoffSampleLaw M).toMeasure.map
      (physicalParityFreshField (K := K) m))
    infer_instance
  have hProductPoly : Integrable
      (fun p : C(K, ℝ) × C(K, ℝ) => (1 + ‖p.2‖) ^ 4)
      (μold.prod μfresh) := hFreshPoly.comp_snd μold
  let bF : ℝ := β * ‖f‖
  let c1 : ℝ := ‖J‖ * bF ^ 2 * σ⁻¹
  let c2 : ℝ := ‖J‖ * bF ^ 2 * β * (σ⁻¹) ^ 2
  let c3 : ℝ := ‖J‖ * bF ^ 2 * β ^ 2 * (σ⁻¹) ^ 3
  let c4 : ℝ := ‖J‖ * bF ^ 2 * β ^ 3 * (σ⁻¹) ^ 4
  let csum : ℝ := c1 + c2 + c3 + c4
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hc3 : 0 ≤ c3 := by positivity
  have hc4 : 0 ≤ c4 := by positivity
  have hcsum : 0 ≤ csum := by
    change 0 ≤ c1 + c2 + c3 + c4
    exact add_nonneg (add_nonneg (add_nonneg hc1 hc2) hc3) hc4
  have hBf (p : C(K, ℝ) × C(K, ℝ)) : ‖B p.1 f‖ ≤ β * ‖f‖ := by
    calc
      ‖B p.1 f‖ ≤ ‖B p.1‖ * ‖f‖ := (B p.1).le_opNorm f
      _ ≤ β * ‖f‖ := mul_le_mul_of_nonneg_right (hBop p.1) (norm_nonneg f)
  have hJb (p : C(K, ℝ) × C(K, ℝ)) :
      ‖J (B p.1 f)‖ ≤ ‖J‖ * (β * ‖f‖) := by
    calc
      ‖J (B p.1 f)‖ ≤ ‖J‖ * ‖B p.1 f‖ := J.le_opNorm _
      _ ≤ ‖J‖ * (β * ‖f‖) :=
        mul_le_mul_of_nonneg_left (hBf p) (norm_nonneg J)
  have hCbf (p : C(K, ℝ) × C(K, ℝ)) :
      ‖C p.2 (B p.1 f)‖ ≤ (‖p.2‖ / σ) * (β * ‖f‖) := by
    calc
      ‖C p.2 (B p.1 f)‖ ≤ ‖C p.2‖ * ‖B p.1 f‖ := (C p.2).le_opNorm _
      _ ≤ (‖p.2‖ / σ) * (β * ‖f‖) :=
        mul_le_mul (hCop p.2) (hBf p) (norm_nonneg (B p.1 f))
          (div_nonneg (norm_nonneg p.2) hσ.le)
  have hprod2 (p : C(K, ℝ) × C(K, ℝ)) :
      ‖C p.2 * B p.1 * C p.2‖ ≤ (‖p.2‖ / σ) * β * (‖p.2‖ / σ) := by
    calc
      ‖C p.2 * B p.1 * C p.2‖ ≤ ‖C p.2 * B p.1‖ * ‖C p.2‖ :=
        norm_mul_le (C p.2 * B p.1) (C p.2)
      _ ≤ (‖C p.2‖ * ‖B p.1‖) * ‖C p.2‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le (C p.2) (B p.1))
          (norm_nonneg (C p.2))
      _ ≤ (‖p.2‖ / σ) * β * (‖p.2‖ / σ) := by
        have hCB : ‖C p.2‖ * ‖B p.1‖ ≤ (‖p.2‖ / σ) * β :=
          mul_le_mul (hCop p.2) (hBop p.1) (norm_nonneg (B p.1))
            (div_nonneg (norm_nonneg p.2) hσ.le)
        exact mul_le_mul hCB (hCop p.2) (norm_nonneg (C p.2))
          (mul_nonneg (div_nonneg (norm_nonneg p.2) hσ.le) hβ)
  have hS2 (p : C(K, ℝ) × C(K, ℝ)) :
      ‖(C p.2 * B p.1 * C p.2) (B p.1 f)‖ ≤
        ((‖p.2‖ / σ) * β * (‖p.2‖ / σ)) * (β * ‖f‖) := by
    calc
      ‖(C p.2 * B p.1 * C p.2) (B p.1 f)‖ ≤
          ‖C p.2 * B p.1 * C p.2‖ * ‖B p.1 f‖ :=
        (C p.2 * B p.1 * C p.2).le_opNorm _
      _ ≤ ((‖p.2‖ / σ) * β * (‖p.2‖ / σ)) * (β * ‖f‖) := by
        have hbound : 0 ≤ (‖p.2‖ / σ) * β * (‖p.2‖ / σ) :=
          mul_nonneg (mul_nonneg (div_nonneg (norm_nonneg p.2) hσ.le) hβ)
            (div_nonneg (norm_nonneg p.2) hσ.le)
        exact mul_le_mul (hprod2 p) (hBf p) (norm_nonneg (B p.1 f)) hbound
  have hprod3 (p : C(K, ℝ) × C(K, ℝ)) :
      ‖C p.2 * B p.1 * C p.2 * B p.1 * C p.2‖ ≤
        (‖p.2‖ / σ) * β * (‖p.2‖ / σ) * β * (‖p.2‖ / σ) := by
    calc
      ‖C p.2 * B p.1 * C p.2 * B p.1 * C p.2‖ ≤
          ‖C p.2 * B p.1 * C p.2 * B p.1‖ * ‖C p.2‖ :=
        norm_mul_le (C p.2 * B p.1 * C p.2 * B p.1) (C p.2)
      _ ≤ (‖C p.2 * B p.1 * C p.2‖ * ‖B p.1‖) * ‖C p.2‖ :=
        mul_le_mul_of_nonneg_right
          (norm_mul_le (C p.2 * B p.1 * C p.2) (B p.1))
          (norm_nonneg (C p.2))
      _ ≤ ((‖C p.2 * B p.1‖ * ‖C p.2‖ * ‖B p.1‖) * ‖C p.2‖) := by
        have hCBC := norm_mul_le (C p.2 * B p.1) (C p.2)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCBC (norm_nonneg (B p.1)))
          (norm_nonneg (C p.2))
      _ ≤ ((‖C p.2‖ * ‖B p.1‖ * ‖C p.2‖ * ‖B p.1‖) * ‖C p.2‖) := by
        gcongr
        exact norm_mul_le (C p.2) (B p.1)
      _ ≤ (‖p.2‖ / σ) * β * (‖p.2‖ / σ) * β * (‖p.2‖ / σ) := by
        gcongr <;> first | exact hCop p.2 | exact hBop p.1
  have hS3 (p : C(K, ℝ) × C(K, ℝ)) :
      ‖(C p.2 * B p.1 * C p.2 * B p.1 * C p.2) (B p.1 f)‖ ≤
        ((‖p.2‖ / σ) * β * (‖p.2‖ / σ) * β * (‖p.2‖ / σ)) *
          (β * ‖f‖) := by
    calc
      ‖(C p.2 * B p.1 * C p.2 * B p.1 * C p.2) (B p.1 f)‖ ≤
          ‖C p.2 * B p.1 * C p.2 * B p.1 * C p.2‖ * ‖B p.1 f‖ :=
        (C p.2 * B p.1 * C p.2 * B p.1 * C p.2).le_opNorm _
      _ ≤ ((‖p.2‖ / σ) * β * (‖p.2‖ / σ) * β * (‖p.2‖ / σ)) *
          (β * ‖f‖) := by
        have hbound : 0 ≤ (‖p.2‖ / σ) * β * (‖p.2‖ / σ) * β * (‖p.2‖ / σ) :=
          mul_nonneg
            (mul_nonneg
              (mul_nonneg (mul_nonneg (div_nonneg (norm_nonneg p.2) hσ.le) hβ)
                (div_nonneg (norm_nonneg p.2) hσ.le)) hβ)
            (div_nonneg (norm_nonneg p.2) hσ.le)
        exact mul_le_mul (hprod3 p) (hBf p) (norm_nonneg (B p.1 f)) hbound
  have hpow (p : C(K, ℝ) × C(K, ℝ)) {k : ℕ} (hk : k ≤ 4) :
      ‖p.2‖ ^ k ≤ (1 + ‖p.2‖) ^ 4 := by
    have hbase : ‖p.2‖ ≤ 1 + ‖p.2‖ := by linarith [norm_nonneg p.2]
    have hbaseOne : 1 ≤ 1 + ‖p.2‖ := by linarith [norm_nonneg p.2]
    calc
      ‖p.2‖ ^ k ≤ (1 + ‖p.2‖) ^ k :=
        pow_le_pow_left₀ (norm_nonneg p.2) hbase k
      _ ≤ (1 + ‖p.2‖) ^ 4 :=
        pow_le_pow_right₀ hbaseOne hk
  have hlinearBound (p : C(K, ℝ) × C(K, ℝ)) :
      ‖linear p‖ ≤ c1 * (1 + ‖p.2‖) ^ 4 := by
    have hlin0 : ‖linear p‖ ≤ c1 * ‖p.2‖ := by
      calc
        ‖linear p‖ ≤ ‖J (B p.1 f)‖ * ‖C p.2 (B p.1 f)‖ := by
          change ‖hilbertG1LinearTerm (B p.1) J f (C p.2)‖ ≤ _
          exact hilbertG1LinearTerm_norm_le (B p.1) J (C p.2) f
        _ ≤ (‖J‖ * (β * ‖f‖)) * ((‖p.2‖ / σ) * (β * ‖f‖)) :=
          mul_le_mul (hJb p) (hCbf p) (norm_nonneg (C p.2 (B p.1 f)))
            (mul_nonneg (norm_nonneg J) (mul_nonneg hβ (norm_nonneg f)))
        _ = c1 * ‖p.2‖ := by
          dsimp only [c1, bF]
          ring
    have hpow1 : ‖p.2‖ ≤ (1 + ‖p.2‖) ^ 4 := by
      simpa using hpow p (k := 1) (by norm_num)
    exact hlin0.trans (mul_le_mul_of_nonneg_left hpow1 hc1)
  have hhessianBound (p : C(K, ℝ) × C(K, ℝ)) :
      ‖hessian p‖ ≤ c2 * (1 + ‖p.2‖) ^ 4 := by
    have hh0 : ‖hessian p‖ ≤ c2 * ‖p.2‖ ^ 2 := by
      calc
        ‖hessian p‖ ≤ ‖J (B p.1 f)‖ *
            ‖(C p.2 * B p.1 * C p.2) (B p.1 f)‖ := by
          change ‖hilbertG1HessianTerm (B p.1) J f (C p.2)‖ ≤ _
          exact hilbertG1HessianTerm_norm_le (B p.1) J (C p.2) f
        _ ≤ (‖J‖ * (β * ‖f‖)) *
            (((‖p.2‖ / σ) * β * (‖p.2‖ / σ)) * (β * ‖f‖)) :=
          mul_le_mul (hJb p) (hS2 p) (norm_nonneg ((C p.2 * B p.1 * C p.2) (B p.1 f)))
            (mul_nonneg (norm_nonneg J) (mul_nonneg hβ (norm_nonneg f)))
        _ = c2 * ‖p.2‖ ^ 2 := by
          dsimp only [c2, bF]
          ring
    exact hh0.trans (mul_le_mul_of_nonneg_left
      (hpow p (k := 2) (by norm_num)) hc2)
  have hcubicBound (p : C(K, ℝ) × C(K, ℝ)) :
      ‖cubic p‖ ≤ c3 * (1 + ‖p.2‖) ^ 4 := by
    have hc0 : ‖cubic p‖ ≤ c3 * ‖p.2‖ ^ 3 := by
      calc
        ‖cubic p‖ ≤ ‖J (B p.1 f)‖ *
            ‖(C p.2 * B p.1 * C p.2 * B p.1 * C p.2) (B p.1 f)‖ := by
          change ‖hilbertG1CubicTerm (B p.1) J f (C p.2)‖ ≤ _
          exact hilbertG1CubicTerm_norm_le (B p.1) J (C p.2) f
        _ ≤ (‖J‖ * (β * ‖f‖)) *
            (((‖p.2‖ / σ) * β * (‖p.2‖ / σ) * β * (‖p.2‖ / σ)) *
              (β * ‖f‖)) :=
          mul_le_mul (hJb p) (hS3 p)
            (norm_nonneg ((C p.2 * B p.1 * C p.2 * B p.1 * C p.2) (B p.1 f)))
            (mul_nonneg (norm_nonneg J) (mul_nonneg hβ (norm_nonneg f)))
        _ = c3 * ‖p.2‖ ^ 3 := by
          dsimp only [c3, bF]
          ring
    exact hc0.trans (mul_le_mul_of_nonneg_left
      (hpow p (k := 3) (by norm_num)) hc3)
  have hquarticBound (p : C(K, ℝ) × C(K, ℝ)) :
      ‖quartic p‖ ≤ c4 * (1 + ‖p.2‖) ^ 4 := by
    have hq0 : ‖quartic p‖ ≤ c4 * ‖p.2‖ ^ 4 := by
      let s := (C p.2 * B p.1 * C p.2) (B p.1 f)
      have hJs : ‖J s‖ ≤ ‖J‖ * (((‖p.2‖ / σ) * β * (‖p.2‖ / σ)) * (β * ‖f‖)) := by
        calc
          ‖J s‖ ≤ ‖J‖ * ‖s‖ := J.le_opNorm _
          _ ≤ ‖J‖ * (((‖p.2‖ / σ) * β * (‖p.2‖ / σ)) * (β * ‖f‖)) :=
            mul_le_mul_of_nonneg_left (hS2 p) (norm_nonneg J)
      have hNs : ‖N p.1 p.2 s‖ ≤
          β * (((‖p.2‖ / σ) * β * (‖p.2‖ / σ)) * (β * ‖f‖)) := by
        calc
          ‖N p.1 p.2 s‖ ≤ ‖N p.1 p.2‖ * ‖s‖ := (N p.1 p.2).le_opNorm _
          _ ≤ β * ‖s‖ := mul_le_mul_of_nonneg_right
            (hNop p.1 p.2) (norm_nonneg s)
          _ ≤ β * (((‖p.2‖ / σ) * β * (‖p.2‖ / σ)) * (β * ‖f‖)) :=
            mul_le_mul_of_nonneg_left (hS2 p) hβ
      calc
        ‖quartic p‖ ≤ ‖J s‖ * ‖N p.1 p.2 s‖ := by
          change ‖hilbertG1QuarticTerm (B p.1) J f (C p.2) (N p.1 p.2)‖ ≤ _
          exact hilbertG1QuarticTerm_norm_le
            (B p.1) J (C p.2) (N p.1 p.2) f
        _ ≤ (‖J‖ * (((‖p.2‖ / σ) * β * (‖p.2‖ / σ)) * (β * ‖f‖))) *
            (β * (((‖p.2‖ / σ) * β * (‖p.2‖ / σ)) * (β * ‖f‖))) :=
          mul_le_mul hJs hNs (norm_nonneg (N p.1 p.2 s))
            (mul_nonneg (norm_nonneg J)
              (mul_nonneg
                (mul_nonneg
                  (mul_nonneg (div_nonneg (norm_nonneg p.2) hσ.le) hβ)
                  (div_nonneg (norm_nonneg p.2) hσ.le))
                (mul_nonneg hβ (norm_nonneg f))))
        _ = c4 * ‖p.2‖ ^ 4 := by
          dsimp only [c4, bF]
          ring
    exact hq0.trans (mul_le_mul_of_nonneg_left
      (hpow p (k := 4) (by norm_num)) hc4)
  have hc1sum : c1 ≤ csum := by dsimp [csum]; linarith [hc2, hc3, hc4]
  have hc2sum : c2 ≤ csum := by dsimp [csum]; linarith [hc1, hc3, hc4]
  have hc3sum : c3 ≤ csum := by dsimp [csum]; linarith [hc1, hc2, hc4]
  have hc4sum : c4 ≤ csum := by dsimp [csum]; linarith [hc1, hc2, hc3]
  have hlinearDom (p : C(K, ℝ) × C(K, ℝ)) :
      ‖linear p‖ ≤ csum * (1 + ‖p.2‖) ^ 4 :=
    (hlinearBound p).trans (mul_le_mul_of_nonneg_right hc1sum (by positivity))
  have hhessianDom (p : C(K, ℝ) × C(K, ℝ)) :
      ‖hessian p‖ ≤ csum * (1 + ‖p.2‖) ^ 4 :=
    (hhessianBound p).trans (mul_le_mul_of_nonneg_right hc2sum (by positivity))
  have hcubicDom (p : C(K, ℝ) × C(K, ℝ)) :
      ‖cubic p‖ ≤ csum * (1 + ‖p.2‖) ^ 4 :=
    (hcubicBound p).trans (mul_le_mul_of_nonneg_right hc3sum (by positivity))
  have hquarticDom (p : C(K, ℝ) × C(K, ℝ)) :
      ‖quartic p‖ ≤ csum * (1 + ‖p.2‖) ^ 4 :=
    (hquarticBound p).trans (mul_le_mul_of_nonneg_right hc4sum (by positivity))
  have hlinearInt : Integrable linear (μold.prod μfresh) := by
    refine (hProductPoly.const_mul csum).mono' hlinearCont.aestronglyMeasurable ?_
    filter_upwards with p
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hcsum (by positivity))] using hlinearDom p
  have hhessianInt : Integrable hessian (μold.prod μfresh) := by
    refine (hProductPoly.const_mul csum).mono' hhessianCont.aestronglyMeasurable ?_
    filter_upwards with p
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hcsum (by positivity))] using hhessianDom p
  have hcubicInt : Integrable cubic (μold.prod μfresh) := by
    refine (hProductPoly.const_mul csum).mono' hcubicCont.aestronglyMeasurable ?_
    filter_upwards with p
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hcsum (by positivity))] using hcubicDom p
  have hquarticInt : Integrable quartic (μold.prod μfresh) := by
    refine (hProductPoly.const_mul csum).mono' hquarticCont.aestronglyMeasurable ?_
    filter_upwards with p
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hcsum (by positivity))] using hquarticDom p
  exact ⟨hlinearInt, hhessianInt, hcubicInt, hquarticInt⟩

private theorem physicalParity_response_pointwise
    {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (R : C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q)) (e : Vec 2)
    (x y : C(K, ℝ)) :
    physicalParityResponseIncrement Q ν σ hν hσ R e (x, y) =
      (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        (physicalParityLinearObservable Q ν σ hν hσ R e (x, y) +
          physicalParityHessianObservable Q ν σ hν hσ R e (x, y) +
          physicalParityCubicObservable Q ν σ hν hσ R e (x, y) +
          physicalParityQuarticObservable Q ν σ hν hσ R e (x, y)) := by
  have h := physicalResponse_fourTerm_identity Q ν σ hν hσ (R x) (R y) e
  have hR : R (x + y) = R x + R y := R.map_add x y
  rw [physicalParityResponseIncrement, hR]
  simp [physicalParityLinearObservable,
    physicalParityHessianObservable, physicalParityCubicObservable,
    physicalParityQuarticObservable, physicalParityCoefficient,
    physicalConstantLoad,
    physicalProjectedInsertion, hilbertG1LinearTerm,
    hilbertG1HessianTerm, hilbertG1CubicTerm, hilbertG1QuarticTerm] at h ⊢
  linarith

/-- In the actual OLD/fresh-shell coupling, the two odd terms in the physical
four-term resolvent identity cancel. The remaining response increment is the
OLD Hessian term and the actual NEW-resolvent quartic term. The product law in
the conclusion is the push-forward of the cutoff law under the completed OLD
field and the next scalar shell. -/
theorem physical_resolvent_parity
    {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (hQ : closure (openCubeSet Q) ⊆ K)
    (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (σ : ℝ) (hσ : 0 < σ) (e : Vec 2)
    (h : ℝ) (hM : PlanarQ3Gaussian M h) :
    Measure.map (physicalParityPairMap (K := K) m)
        (Cutoff.cutoffSampleLaw M).toMeasure =
        physicalParityProductLaw M m ∧
      (∫ p, physicalParityLinearObservable Q M.nu σ M.nu_pos hσ
        (physicalResponseRestriction Q hQ) e p
        ∂(physicalParityProductLaw M m) = 0) ∧
      (∫ p, physicalParityCubicObservable Q M.nu σ M.nu_pos hσ
        (physicalResponseRestriction Q hQ) e p
        ∂(physicalParityProductLaw M m) = 0) ∧
      (∫ p, physicalParityResponseIncrement Q M.nu σ M.nu_pos hσ
        (physicalResponseRestriction Q hQ) e p
        ∂(physicalParityProductLaw M m) =
        (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
          ((∫ p, physicalParityHessianObservable Q M.nu σ M.nu_pos hσ
              (physicalResponseRestriction Q hQ) e p
              ∂(physicalParityProductLaw M m)) +
            (∫ p, physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ
              (physicalResponseRestriction Q hQ) e p
              ∂(physicalParityProductLaw M m)))) := by
  let U := openCubeSet Q
  let R := physicalResponseRestriction Q hQ
  let ρ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := olderField K m
  let Y := physicalParityFreshField (K := K) m
  let μold := physicalParityOldMarginal (K := K) M m
  let μfresh := physicalParityFreshMarginal (K := K) M m
  let A := physicalParityCoefficient Q σ hσ R
  let α := M.nu / σ
  let hα : 0 < α := div_pos M.nu_pos hσ
  let B := physicalParityOldInverse Q M.nu σ M.nu_pos hσ R
  let C := physicalParityInsertionBlock Q σ hσ R
  let N : C(K, ℝ) → C(K, ℝ) → physicalParityHilbert Q →L[ℝ]
      physicalParityHilbert Q := fun x y =>
    pureFluxBlockInverse α hα (A x + A y)
  let J := pureFluxParity (Y := HilbertVectorL2 U)
    (X := (physicalPotentialSpace Q).toSubmodule)
  let f : pureFluxPair (Y := HilbertVectorL2 U)
      (X := (physicalPotentialSpace Q).toSubmodule) :=
    pureFluxLoad (Y := HilbertVectorL2 U)
      (X := (physicalPotentialSpace Q).toSubmodule)
      (physicalConstantLoad Q e)
  let linear : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityLinearObservable Q M.nu σ M.nu_pos hσ R e
  let hessian : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityHessianObservable Q M.nu σ M.nu_pos hσ R e
  let cubic : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityCubicObservable Q M.nu σ M.nu_pos hσ R e
  let quartic : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityQuarticObservable Q M.nu σ M.nu_pos hσ R e
  let responseIncrement : C(K, ℝ) × C(K, ℝ) → ℝ :=
    physicalParityResponseIncrement Q M.nu σ M.nu_pos hσ R e
  change Measure.map (fun ω : Cutoff.CutoffSample 2 => (X ω, Y ω)) ρ =
        μold.prod μfresh ∧
      (∫ p, linear p ∂(μold.prod μfresh) = 0) ∧
      (∫ p, cubic p ∂(μold.prod μfresh) = 0) ∧
      (∫ p, responseIncrement p ∂(μold.prod μfresh) =
        (MeasureTheory.volume U).toReal⁻¹ *
          ((∫ p, hessian p ∂(μold.prod μfresh)) +
            (∫ p, quartic p ∂(μold.prod μfresh))))
  have hX : Measurable X := measurable_olderField K ell m hK
  have hY : Measurable Y := (measurable_shellFieldScalarRestriction K).comp
    ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have hJoint : ρ.map (fun ω => (X ω, Y ω)) = μold.prod μfresh := by
    have hi := (indepFun_olderField_freshShell K M ell m hK).map_prod_eq_prod_map_map
      hX.aemeasurable hY.aemeasurable
    change ρ.map (fun ω => (X ω, Y ω)) = (ρ.map X).prod (ρ.map Y) at hi
    exact hi
  letI : SFinite μold := by
    change SFinite (ρ.map X)
    infer_instance
  letI : SFinite μfresh := by
    change SFinite (ρ.map Y)
    infer_instance
  let negFresh : C(K, ℝ) → C(K, ℝ) := fun y => -y
  have hnegFreshMeas : Measurable negFresh := by
    change Measurable (fun y : C(K, ℝ) => -y)
    fun_prop
  have hYlaw : μfresh =
      (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
        (shellFieldScalarRestriction K) := by
    calc
      μfresh = (ρ.map (fun ω : Cutoff.CutoffSample 2 => ω.1 (m + 1))).map
          (shellFieldScalarRestriction K) := by
            dsimp [μfresh, Y]
            rw [Measure.map_map (measurable_shellFieldScalarRestriction K)
              ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)]
            rfl
      _ = (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
          (shellFieldScalarRestriction K) := by
            rw [← Model.map_freshShell_eq_shellMarginalLaw M m]
  have hnegShell : Measure.map (ShellField.negate (d := 2))
      (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure =
        (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure :=
    Algsuperdiff.Section3.Provider.Corrector.map_negate_shellMarginalLaw M (m + 1)
  have hneg : Measure.map negFresh μfresh = μfresh := by
    rw [hYlaw]
    calc
      Measure.map negFresh
          ((ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
            (shellFieldScalarRestriction K)) =
        (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
          (fun j => -shellFieldScalarRestriction K j) := by
            rw [Measure.map_map hnegFreshMeas
              (measurable_shellFieldScalarRestriction K)]
            rfl
      _ = (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
          (fun j => shellFieldScalarRestriction K (ShellField.negate j)) := by
            congr 1
            funext j
            exact (shellFieldScalarRestriction_negate K j).symm
      _ = ((ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
          (ShellField.negate (d := 2))).map
            (shellFieldScalarRestriction K) := by
              exact (Measure.map_map (measurable_shellFieldScalarRestriction K)
                ShellField.measurable_negate).symm
      _ = (ShellField.shellMarginalLaw M.P (m + 1)).toMeasure.map
          (shellFieldScalarRestriction K) := by
        rw [hnegShell]
  have hflip : Measure.map (fun p : C(K, ℝ) × C(K, ℝ) => (p.1, negFresh p.2))
      (μold.prod μfresh) = μold.prod μfresh :=
    product_fresh_flip_preserves μold μfresh negFresh hnegFreshMeas hneg
  let negPair : C(K, ℝ) × C(K, ℝ) → C(K, ℝ) × C(K, ℝ) :=
    fun p => (p.1, negFresh p.2)
  obtain ⟨hlinearInt, hhessianInt, hcubicInt, hquarticInt⟩ :=
    physicalParity_terms_integrable Q hQ M m σ hσ e h hM
  have hnegPairMeas : Measurable negPair := by
    change Measurable (fun p : C(K, ℝ) × C(K, ℝ) => (p.1, -p.2))
    fun_prop
  have hMparity (p : C(K, ℝ) × C(K, ℝ)) :
      (physicalParityOldBlock Q M.nu σ hσ R p.1).adjoint * J =
        J * physicalParityOldBlock Q M.nu σ hσ R p.1 := by
    exact physicalBlock_parityAdjoint α (A p.1)
  have hCparity (p : C(K, ℝ) × C(K, ℝ)) :
      (C p.2).adjoint * J = J * C p.2 := by
    exact physicalBlock_parityAdjoint 0 (A p.2)
  have hBM (p : C(K, ℝ) × C(K, ℝ)) :
      B p.1 * physicalParityOldBlock Q M.nu σ hσ R p.1 = 1 :=
    pureFluxBlockInverse_right α hα (A p.1)
  have hMB (p : C(K, ℝ) × C(K, ℝ)) :
      physicalParityOldBlock Q M.nu σ hσ R p.1 * B p.1 = 1 :=
    pureFluxBlockInverse_left α hα (A p.1)
  have hMN (p : C(K, ℝ) × C(K, ℝ)) :
      (physicalParityOldBlock Q M.nu σ hσ R p.1 + C p.2) * N p.1 p.2 = 1 :=
    (physicalParity_newInverse_two_sided Q M.nu σ M.nu_pos hσ R
      p.1 p.2).1
  have hNM (p : C(K, ℝ) × C(K, ℝ)) :
      N p.1 p.2 * (physicalParityOldBlock Q M.nu σ hσ R p.1 + C p.2) = 1 :=
    (physicalParity_newInverse_two_sided Q M.nu σ M.nu_pos hσ R
      p.1 p.2).2
  have hBneg (p : C(K, ℝ) × C(K, ℝ)) : B (negPair p).1 = B p.1 := rfl
  have hCneg (p : C(K, ℝ) × C(K, ℝ)) : C (negPair p).2 = -(C p.2) := by
    change physicalParityInsertionBlock Q σ hσ R (-p.2) =
      -physicalParityInsertionBlock Q σ hσ R p.2
    exact physicalParity_insertion_neg Q σ hσ R p.2
  have hf : J f = f := by simp [J, f, pureFluxParity, pureFluxLoad]
  have hparity := resolvent_hilbert_parity_random_old
    (μold.prod μfresh) negPair hnegPairMeas hflip
    (fun p => physicalParityOldBlock Q M.nu σ hσ R p.1)
    (fun p => B p.1) J hMparity hBM hMB
    (fun p => C p.2) (fun p => N p.1 p.2)
    hCparity hMN hNM hBneg hCneg f hf
    hlinearInt hhessianInt hcubicInt hquarticInt
  let eH := physicalConstantLoad Q e
  let volInv := (MeasureTheory.volume U).toReal⁻¹
  let qdiff : C(K, ℝ) × C(K, ℝ) → ℝ := fun p =>
    ⟪f, N p.1 p.2 f⟫_ℝ - ⟪f, B p.1 f⟫_ℝ
  have hquadPoint (p : C(K, ℝ) × C(K, ℝ)) :
      qdiff p = linear p + hessian p + cubic p + quartic p := by
    change ⟪f, N p.1 p.2 f⟫_ℝ - ⟪f, B p.1 f⟫_ℝ = _
    have h := resolvent_four_term_hilbert_pairing
      (physicalParityOldBlock Q M.nu σ hσ R p.1) (C p.2) (B p.1)
      (N p.1 p.2) J (hMparity p) (hCparity p) (hBM p) (hMB p)
      (hMN p) (hNM p) f hf
    change ⟪f, N p.1 p.2 f⟫_ℝ - ⟪f, B p.1 f⟫_ℝ =
      hilbertG1LinearTerm (B p.1) J f (C p.2) +
        hilbertG1HessianTerm (B p.1) J f (C p.2) +
        hilbertG1CubicTerm (B p.1) J f (C p.2) +
        hilbertG1QuarticTerm (B p.1) J f (C p.2) (N p.1 p.2)
    exact h
  let fourTerms : C(K, ℝ) × C(K, ℝ) → ℝ := fun p =>
    (linear p + hessian p) + (cubic p + quartic p)
  have hfourInt : Integrable fourTerms (μold.prod μfresh) := by
    have hi := (hlinearInt.add hhessianInt).add (hcubicInt.add hquarticInt)
    change Integrable (fun p => (linear p + hessian p) + (cubic p + quartic p)) _
    exact hi
  have hqdiffInt : Integrable qdiff (μold.prod μfresh) := by
    apply hfourInt.congr
    filter_upwards with p
    calc
      fourTerms p = linear p + hessian p + cubic p + quartic p := by
        simp only [fourTerms]
        ring
      _ = qdiff p := (hquadPoint p).symm
  have hvol : 0 < (MeasureTheory.volume U).toReal := by
    dsimp [U]
    rw [volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal]
    exact cubeVolume_pos Q
  have hparityLast :
      (∫ p, qdiff p ∂(μold.prod μfresh)) =
        (∫ p, hessian p ∂(μold.prod μfresh)) +
          (∫ p, quartic p ∂(μold.prod μfresh)) := by
    simpa [qdiff, hessian, quartic, B, N, J, f,
      physicalParityOldInverse, physicalParityCoefficient,
      A, C, physicalParityInsertionBlock, physicalParityNewInverse,
      physicalParityHessianObservable, physicalParityQuarticObservable,
      hilbertG1HessianTerm, hilbertG1QuarticTerm] using hparity.2.2
  have hresponsePoint (p : C(K, ℝ) × C(K, ℝ)) :
      responseIncrement p = volInv * qdiff p := by
    change physicalParityResponseIncrement Q M.nu σ M.nu_pos hσ R e p =
      (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ * qdiff p
    rw [physicalParity_response_pointwise Q M.nu σ M.nu_pos hσ R e p.1 p.2]
    congr 1
    exact (hquadPoint p).symm
  refine ⟨hJoint, hparity.1, hparity.2.1, ?_⟩
  calc
    (∫ p, responseIncrement p ∂(μold.prod μfresh)) =
        ∫ p, volInv * qdiff p ∂(μold.prod μfresh) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hresponsePoint
    _ = volInv * ∫ p, qdiff p ∂(μold.prod μfresh) :=
          by rw [integral_const_mul]
    _ = volInv *
        ((∫ p, hessian p ∂(μold.prod μfresh)) +
          (∫ p, quartic p ∂(μold.prod μfresh))) := by
            rw [hparityLast]

end

end ASDExplicitGamma.Scalar
