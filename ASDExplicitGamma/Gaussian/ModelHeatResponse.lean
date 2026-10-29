module

public import ASDExplicitGamma.Gaussian.ModelHeat
public import ASDExplicitGamma.Response.Analytic

/-! # The framed trace response as a Gaussian heat observable -/

@[expose] public section

open MeasureTheory Filter Set
open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

section Growth
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem c2_directional_differentiable {f : E → ℝ} (hf : ContDiff ℝ 2 f) (w : E) :
    Differentiable ℝ (fun x => fderiv ℝ f x w) := by
  exact ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply contDiff_const).differentiable_one

/-- Polynomial C² bounds are preserved by addition. -/
theorem hasPolynomiallyBoundedC2Derivatives_add {f g : E → ℝ}
    (hf : HasPolynomiallyBoundedC2Derivatives f) (hg : HasPolynomiallyBoundedC2Derivatives g) :
    HasPolynomiallyBoundedC2Derivatives (fun x => f x + g x) := by
  obtain ⟨hf2, C, hC, d, hvf, hdf, hhf⟩ := hf
  obtain ⟨hg2, B, hB, e, hvg, hdg, hhg⟩ := hg
  have hfd : Differentiable ℝ f := hf2.differentiable (by norm_num)
  have hgd : Differentiable ℝ g := hg2.differentiable (by norm_num)
  have hp (x : E) : (1 + ‖x‖) ^ d ≤ (1 + ‖x‖) ^ (d + e) ∧
      (1 + ‖x‖) ^ e ≤ (1 + ‖x‖) ^ (d + e) := by
    constructor <;> apply pow_le_pow_right₀ (by linarith [norm_nonneg x]) <;> omega
  have hb (x : E) : C * (1 + ‖x‖) ^ d + B * (1 + ‖x‖) ^ e ≤
      (C + B) * (1 + ‖x‖) ^ (d + e) := by
    calc
      _ ≤ C * (1 + ‖x‖) ^ (d + e) + B * (1 + ‖x‖) ^ (d + e) :=
        add_le_add (mul_le_mul_of_nonneg_left (hp x).1 hC) (mul_le_mul_of_nonneg_left (hp x).2 hB)
      _ = _ := by ring
  refine ⟨hf2.add hg2, C + B, add_nonneg hC hB, d + e, ?_, ?_, ?_⟩
  · intro x
    exact (abs_add_le _ _).trans ((add_le_add (hvf x) (hvg x)).trans (hb x))
  · intro x
    rw [fderiv_fun_add (hfd x) (hgd x)]
    exact (norm_add_le _ _).trans ((add_le_add (hdf x) (hdg x)).trans (hb x))
  · intro x u w
    have hfun : (fun z => fderiv ℝ (fun y => f y + g y) z w) =
        fun z => fderiv ℝ f z w + fderiv ℝ g z w := by
      funext z
      rw [fderiv_fun_add (hfd z) (hgd z), add_apply]
    rw [hfun, fderiv_fun_add (c2_directional_differentiable hf2 w x)
      (c2_directional_differentiable hg2 w x), add_apply]
    calc
      _ ≤ |fderiv ℝ (fun z => fderiv ℝ f z w) x u| +
          |fderiv ℝ (fun z => fderiv ℝ g z w) x u| := abs_add_le _ _
      _ ≤ C * (1 + ‖x‖) ^ d * ‖u‖ * ‖w‖ + B * (1 + ‖x‖) ^ e * ‖u‖ * ‖w‖ :=
        add_le_add (hhf x u w) (hhg x u w)
      _ = (C * (1 + ‖x‖) ^ d + B * (1 + ‖x‖) ^ e) * ‖u‖ * ‖w‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg u)) (norm_nonneg w)

/-- Subtracting a constant preserves polynomial C² bounds. -/
theorem hasPolynomiallyBoundedC2Derivatives_sub_const {f : E → ℝ}
    (hf : HasPolynomiallyBoundedC2Derivatives f) (b : ℝ) :
    HasPolynomiallyBoundedC2Derivatives (fun x => f x - b) := by
  have hc : HasPolynomiallyBoundedC2Derivatives (fun _ : E => -b) := by
    refine ⟨contDiff_const, |b|, abs_nonneg b, 0, ?_, ?_, ?_⟩
    · intro x
      simp only [abs_neg, pow_zero, mul_one, le_refl]
    · intro x
      simp only [fderiv_const_apply, norm_zero, pow_zero, mul_one]
      exact abs_nonneg b
    · intro x u w
      simp only [fderiv_const_apply, zero_apply, abs_zero, pow_zero, mul_one]
      positivity
  simpa only [sub_eq_add_neg] using hasPolynomiallyBoundedC2Derivatives_add hf hc

/-- The compact-continuous and bounded-continuous carriers give identical polynomial C²
control under their canonical linear isometry. -/
theorem hasPolynomiallyBoundedC2Derivatives_comp_isometry
    (L : E →ₗᵢ[ℝ] F) {f : F → ℝ} (hf : HasPolynomiallyBoundedC2Derivatives f) :
    HasPolynomiallyBoundedC2Derivatives (fun x => f (L x)) := by
  obtain ⟨hf2, C, hC, d, hv, hd, hh⟩ := hf
  have hfd := hf2.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  have hderiv (x : E) : fderiv ℝ (fun y => f (L y)) x =
      (fderiv ℝ f (L x)).comp L.toContinuousLinearMap :=
    (hfd (L x)).hasFDerivAt.comp x L.toContinuousLinearMap.hasFDerivAt |>.fderiv
  refine ⟨hf2.comp L.contDiff, C, hC, d, ?_, ?_, ?_⟩
  · intro x
    simpa only [L.norm_map] using hv (L x)
  · intro x
    rw [hderiv]
    calc
      _ ≤ ‖fderiv ℝ f (L x)‖ * ‖L.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ f (L x)‖ * 1 := mul_le_mul_of_nonneg_left L.norm_toContinuousLinearMap_le (norm_nonneg _)
      _ ≤ C * (1 + ‖x‖) ^ d := by simpa only [mul_one, L.norm_map] using hd (L x)
  · intro x u w
    have hfun : (fun z => fderiv ℝ (fun y => f (L y)) z w) =
        fun z => fderiv ℝ f (L z) (L w) := by
      funext z
      rw [hderiv]
      rfl
    rw [hfun]
    have hd2 := (c2_directional_differentiable hf2 (L w) (L x)).hasFDerivAt.comp x
      L.toContinuousLinearMap.hasFDerivAt
    rw [show fderiv ℝ (fun z => fderiv ℝ f (L z) (L w)) x = _ from hd2.fderiv]
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap, L.norm_map] using hh (L x) (L u) (L w)

end Growth

/-- Compact observation carrier for an origin-cube response. -/
instance modelHeatCubeClosureCompact (q : ℤ) : CompactSpace (closure (cubeSet (originCube 2 q))) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet (originCube 2 q)).isCompact_closure

/-- The framed coarse trace defect, as an observable of the physical scalar skew coefficient. -/
noncomputable def modelTraceObservable (q : ℤ) (ν σ : ℝ) :
    C(closure (cubeSet (originCube 2 q)), ℝ) → ℝ := fun k =>
  traceDefect (cubeSet (originCube 2 q))
    (responsePlanarCoefficientField ν
      (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ k)) σ

/-- The trace observable is the four-load response, with the same physical viscosity and frame. -/
theorem modelTraceObservable_eq_fourLoad (q : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : C(closure (cubeSet (originCube 2 q)), ℝ)) :
    modelTraceObservable q ν σ k =
      (∑ i : Fin 2,
        (responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 q))
          (volume_cubeSet_toReal_pos (originCube 2 q)) ν σ hν hσ (orthonormalFrameLoad i 1)
          (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ k) +
        responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 q))
          (volume_cubeSet_toReal_pos (originCube 2 q)) ν σ hν hσ (orthonormalFrameLoad i (-1))
          (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ k))) - 4 :=
  (responseFrameEnergyObservable_fourLoad_eq_traceDefect q ν σ hν hσ _).symm

/-- The source trace response has the exact C² polynomial bounds required by heat insertion. -/
theorem modelTraceObservable_hasPolynomiallyBoundedC2Derivatives
    (q : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) :
    HasPolynomiallyBoundedC2Derivatives (modelTraceObservable q ν σ) := by
  let L := (ContinuousMap.linearIsometryBoundedOfCompact
    (closure (cubeSet (originCube 2 q))) ℝ ℝ).toLinearIsometry
  let E (i : Fin 2) (r : ℝ) : C(closure (cubeSet (originCube 2 q)), ℝ) → ℝ := fun k =>
    responseFrameEnergyObservable (measurableSet_cubeSet (originCube 2 q))
      (volume_cubeSet_toReal_pos (originCube 2 q)) ν σ hν hσ (orthonormalFrameLoad i r) (L k)
  have hE (i : Fin 2) (r : ℝ) : HasPolynomiallyBoundedC2Derivatives (E i r) :=
    hasPolynomiallyBoundedC2Derivatives_comp_isometry L
      (responseFrameEnergyObservable_hasPolynomiallyBoundedC2Derivatives
        (measurableSet_cubeSet (originCube 2 q)) (volume_cubeSet_toReal_pos (originCube 2 q))
        ν σ hν hσ (orthonormalFrameLoad i r))
  have heq : modelTraceObservable q ν σ = fun k =>
      ((E 0 1 k + E 0 (-1) k) + (E 1 1 k + E 1 (-1) k)) - 4 := by
    funext k
    simpa only [Fin.sum_univ_two, E, L, LinearIsometryEquiv.coe_toLinearIsometry] using modelTraceObservable_eq_fourLoad q ν σ hν hσ k
  rw [heq]
  exact hasPolynomiallyBoundedC2Derivatives_sub_const
    (hasPolynomiallyBoundedC2Derivatives_add
      (hasPolynomiallyBoundedC2Derivatives_add (hE 0 1) (hE 0 (-1)))
      (hasPolynomiallyBoundedC2Derivatives_add (hE 1 1) (hE 1 (-1)))) 4

theorem modelTraceObservable_nonneg (q : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : C(closure (cubeSet (originCube 2 q)), ℝ)) :
    0 ≤ modelTraceObservable q ν σ k :=
  traceDefect_nonneg_of_ellipticFieldOn_triCube hν
    (responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet (originCube 2 q)) ν hν _) hσ

private theorem planarCoefficient_eq_of_symmPart (ν : ℝ) (A : Mat 2)
    (hA : symmPart A = ν • (1 : Mat 2)) : responsePlanarCoefficient ν (A 1 0) = A := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  norm_num [symmPart, Matrix.smul_apply, Matrix.one_apply] at h00 h11 h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ] <;> linarith

private theorem symmPart_modelInserted (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    symmPart (Model.partialInsertedCoefficient M m t ω x) = M.nu • (1 : Mat 2) := by
  have ha := Cutoff.symmPart_coefficientCutoff M.nu m ω x
  ext i j
  have hb := congrFun (congrFun ha i) j
  have hj := (ω.1 (m + 1)).skew_entry x i j
  change (Cutoff.coefficientCutoff M.nu m ω x i j +
    Cutoff.coefficientCutoff M.nu m ω x j i) / 2 = (M.nu • (1 : Mat 2)) i j at hb
  change ((Cutoff.coefficientCutoff M.nu m ω x i j + Real.sqrt t * ω.1 (m + 1) x i j) +
    (Cutoff.coefficientCutoff M.nu m ω x j i + Real.sqrt t * ω.1 (m + 1) x j i)) / 2 = _
  rw [hj]
  linarith

/-- The compact coefficient observable is exactly the actual partially inserted coarse response.
The Tietze extension used to present the response does not change its value on the cube. -/
theorem modelTraceObservable_inserted_eq_traceDefect
    (q : ℤ) (M : ABKModel 2) (ell m : ℤ)
    (hK : closure (cubeSet (originCube 2 q)) ⊆ openCubeSet (originCube 2 ell))
    (σ t : ℝ) (ω : Cutoff.CutoffSample 2) :
    modelTraceObservable q M.nu σ
      (modelInsertedScalar (closure (cubeSet (originCube 2 q))) m t ω) =
      traceDefect (cubeSet (originCube 2 q)) (Model.partialInsertedCoefficient M m t ω).toFun σ := by
  have heq : ∀ x ∈ cubeSet (originCube 2 q),
      responsePlanarCoefficientField M.nu
        (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ
          (modelInsertedScalar (closure (cubeSet (originCube 2 q))) m t ω)) x =
        Model.partialInsertedCoefficient M m t ω x := by
    intro x hx
    rw [responsePlanarCoefficientField, responseCoefficientExtension_eq _ hx,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply,
      modelInsertedScalar_apply _ M ell m hK]
    exact planarCoefficient_eq_of_symmPart M.nu _ (symmPart_modelInserted M m t ω x)
  have hae := (ae_restrict_mem (μ := volume) (measurableSet_cubeSet (originCube 2 q))).mono heq
  unfold modelTraceObservable traceDefect
  rw [coarseBlockMatrix_congr_of_ae_eq hae]

/-- Every compact observation set fits in a deterministic larger origin cube. -/
theorem exists_originCube_containing_compact (K : Set (Vec 2)) (hK : IsCompact K) :
    ∃ ell : ℤ, K ⊆ openCubeSet (originCube 2 ell) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 3)).eventually_gt_atTop (2 * R)).exists
  refine ⟨(n : ℤ), ?_⟩
  intro x hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hcoord : |x i| ≤ R := (norm_le_pi_norm x i).trans (hR x hx)
  have hr : |x i| < (1 / 2 : ℝ) * (3 : ℝ) ^ (n : ℤ) := by
    simp only [zpow_natCast]
    linarith
  constructor
  · linarith [neg_abs_le (x i)]
  · exact (le_abs_self (x i)).trans_lt hr

end ASDExplicitGamma.Gaussian
