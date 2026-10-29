/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackCellEnergy
public import ASDExplicitGamma.Inverse.BankInterfaces
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.BridgeGlobalBank
public import ASDExplicitGamma.Scalar.InverseHistoryBlocks

/-! The OLD global inverse bank applied to the physical population of
side-`(m-5)` cells of `Q_{m+129}`: the actual inverse-history maximum `B`
satisfies the bank's split `B ≤ b + R*` with `‖B‖₁₂₈ ≤ b`, `‖R*‖₁₂₈ ≤ ε`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Inverse
open Algsuperdiff.Section3
open scoped BigOperators ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem descendants_split (Q : TriadicCube 2) (j n : ℕ) :
    descendantsAtDepth Q (j + n) =
      (descendantsAtDepth Q j).biUnion (fun R => descendantsAtDepth R n) := by
  classical
  ext S
  rw [Finset.mem_biUnion]
  constructor
  · intro hS
    induction n generalizing S with
    | zero =>
        refine ⟨S, ?_, by simp⟩
        simpa using hS
    | succ n ih =>
        rw [← add_assoc, mem_descendantsAtDepth_succ_iff] at hS
        obtain ⟨S', hS', hchild⟩ := hS
        obtain ⟨R, hR, hS'R⟩ := ih S' hS'
        refine ⟨R, hR, ?_⟩
        rw [mem_descendantsAtDepth_succ_iff]
        exact ⟨S', hS'R, hchild⟩
  · rintro ⟨R, hR, hS⟩
    exact mem_descendantsAtDepth_add hR hS

/-- The frame-normalized cell history is `σ̄` times the physical inverse history. -/
theorem cell_inverse_history_frame (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    lemmaVInverseHistory U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (oldCutoffSkewCoefficient m U ω)) ((3 : ℝ) ^ (1 / 4 : ℝ)) =
      (Annealed.sigmaBar M m : ℝ) * lemmaVInverseHistory U
        (Cutoff.coefficientCutoff M.nu m ω).toFun ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
  let σ : ℝ := Annealed.sigmaBar M m
  have hσ : 0 < σ := (Annealed.sigmaBar M m).property
  let phys := (Cutoff.coefficientCutoff M.nu m ω).toFun
  set aU := responseFramePlanarCoefficientField M.nu σ (oldCutoffSkewCoefficient m U ω) with haU
  have hEllPhys := Cutoff.isEllipticFieldOn_coefficientCutoff_cube M m ω U
  have hEllA := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U) M.nu σ M.nu_pos hσ (oldCutoffSkewCoefficient m U ω)
  have hmatrix (R : TriadicCube 2) (j : ℕ) (hR : R ∈ descendantsAtDepth U j) :
      coarseBlockMatrix (cubeSet R) aU =
        frameMatrix σ (coarseBlockMatrix (cubeSet R) phys) := by
    have hsub := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have hae : aU =ᵐ[volume.restrict (openCubeSet R)]
        responseFramePlanarCoefficientField M.nu σ
          (oldSignedCellCoefficient U R hsub (oldCutoffSkewCoefficient m U ω)) := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      change responsePlanarCoefficient (M.nu / σ)
          (responseCoefficientExtension (oldCutoffSkewCoefficient m U ω) x / σ) =
        responsePlanarCoefficient (M.nu / σ)
          (responseCoefficientExtension
            (oldSignedCellCoefficient U R hsub (oldCutoffSkewCoefficient m U ω)) x / σ)
      rw [responseCoefficientExtension_eq _ (hsub hx),
        responseCoefficientExtension_eq _ hx]
      rfl
    rw [Variational.cube_coarseMatrix_eq_open R aU, coarseBlockMatrix_congr_of_ae_eq hae,
      smooth_feedback_cell_coarse_eq_response M m U R hsub ω]
    rfl
  have hdepth (j : ℕ) : lemmaVInverseDepthMax U aU j =
      σ * lemmaVInverseDepthMax U phys j := by
    rw [← Scalar.inverse_history_framed_depth_max U phys hEllPhys σ hσ j]
    unfold lemmaVInverseDepthMax
    apply Book.Ch02.finsetSupReal_congr
    intro R hR
    have hmatrixR := hmatrix R j hR
    have hlow := congrArg (fun A : BlockMat 2 => A.lowerRight) hmatrixR
    apply congrArg Book.Ch02.matrixNorm
    rw [Scalar.inverse_history_lowerRight R aU
      (hEllA.mono (measurableSet_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR))]
    rw [hlow]
    first | rfl | simp [frameMatrix]
  unfold lemmaVInverseHistory
  have hfun : (fun k : ℕ => (((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ k * lemmaVInverseDepthMax U aU k) =
      fun k => σ * ((((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ k * lemmaVInverseDepthMax U phys k) := by
    funext k; rw [hdepth k]; ring
  rw [hfun, tsum_mul_left]
  ring


theorem ofReal_finsetSupReal {α : Type*} (s : Finset α) (hs : s.Nonempty) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x) :
    ENNReal.ofReal (Book.Ch02.finsetSupReal s f) = s.sup (fun x => ENNReal.ofReal (f x)) := by
  classical
  have hbdd : BddAbove (f '' (↑s : Set α)) := ((Set.toFinite _).image f).bddAbove
  have h1 : Book.Ch02.finsetSupReal s f = s.sup' hs f := by
    apply le_antisymm
    · exact Book.Ch02.finsetSupReal_le s hs (fun x hx => Finset.le_sup' f hx)
    · refine Finset.sup'_le hs f ?_
      intro x hx
      unfold Book.Ch02.finsetSupReal
      exact le_csSup hbdd ⟨x, hx, rfl⟩
  rw [h1]
  apply le_antisymm
  · obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup' hs f
    rw [hxe]
    exact Finset.le_sup (f := fun x => ENNReal.ofReal (f x)) hx
  · apply Finset.sup_le
    intro x hx
    exact ENNReal.ofReal_le_ofReal (Finset.le_sup' f hx)


theorem partialInserted_zero (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) :
    (Model.partialInsertedCoefficient M m 0 ω).toFun =
      (Cutoff.coefficientCutoff M.nu m ω).toFun := by
  funext x i k
  change Cutoff.coefficientCutoff M.nu m ω x i k +
    Real.sqrt 0 * (ω.1 (m + 1)).forgetShell x i k = _
  rw [Real.sqrt_zero, zero_mul, add_zero]

/-- The actual inverse-history maximum is the bank's grouped history. -/
theorem Bhist_eq_grouped (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    ENNReal.ofReal (bhist M m Q 134 ω) =
      inverseBankGroupedHistory (descendantsAtDepth Q 89)
        (fun i => descendantsAtDepth i 45) M m (m + 40)
        (bankPartialInsertionWeights m 1 0) ω := by
  classical
  have hD : descendantsAtDepth Q 134 =
      (descendantsAtDepth Q 89).biUnion (fun i => descendantsAtDepth i 45) :=
    descendants_split Q 89 45
  have hfam (i : TriadicCube 2) :
      bankFiniteRootHistoryMax (descendantsAtDepth i 45) M m (m + 40)
        (bankPartialInsertionWeights m 1 0) ω =
      (descendantsAtDepth i 45).sup
        (fun U => bankRootInverseHistory U M m (m + 40)
          (bankPartialInsertionWeights m 1 0) ω) := by
    unfold bankFiniteRootHistoryMax historyFiniteMax
    change (descendantsAtDepth i 45).attach.sup
      (fun U => bankRootInverseHistory U.1 M m (m + 40)
        (bankPartialInsertionWeights m 1 0) ω) = _
    exact Finset.sup_attach (descendantsAtDepth i 45)
      (fun U => bankRootInverseHistory U M m (m + 40)
        (bankPartialInsertionWeights m 1 0) ω)
  have hbank (U : TriadicCube 2) :
      bankRootInverseHistory U M m (m + 40) (bankPartialInsertionWeights m 1 0) ω =
        ENNReal.ofReal (lemmaVInverseHistory U
          (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
            (oldCutoffSkewCoefficient m U ω)) ((3 : ℝ) ^ (1 / 4 : ℝ))) := by
    have ha : attenuatedCoefficient M m (m + 40) (bankPartialInsertionWeights m 1 0) ω =
        (Cutoff.coefficientCutoff M.nu m ω).toFun := by
      have := bank_one_pass_partial_coefficient M m 1 (by norm_num) 0 ω
      rw [this]
      simpa using partialInserted_zero M m ω
    rw [bank_root_history_physical U M m (m + 40) (bankPartialInsertionWeights m 1 0) ω _ ha
      (Cutoff.isEllipticFieldOn_coefficientCutoff_cube M m ω U),
      cell_inverse_history_frame M m U ω]
  unfold inverseBankGroupedHistory historyFiniteMax
  simp_rw [hfam, hbank]
  rw [← Finset.sup_biUnion, ← hD]
  unfold bhist smoothFeedbackSourceHistoryMaximum
  have hne : (Finset.univ : Finset (OldSignedCellIndex Q 134)).Nonempty := by
    have : (descendantsAtDepth Q 134).card ≠ 0 := by
      rw [descendantsAtDepth_card]; positivity
    obtain ⟨U, hU⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero this)
    exact ⟨⟨U, hU⟩, Finset.mem_univ _⟩
  rw [ofReal_finsetSupReal _ hne _ (fun U _ => lemmaVInverseHistory_nonneg U.val _
    (Real.one_lt_rpow (by norm_num) (by norm_num)))]
  have hk (U : OldSignedCellIndex Q 134) :
      oldSignedCellCoefficient Q U.val
        (openCubeSet_subset_of_mem_descendantsAtDepth U.property)
        (oldCutoffSkewCoefficient m Q ω) = oldCutoffSkewCoefficient m U.val ω :=
    smooth_feedback_cell_coefficient_restrict m Q U.val _ ω
  simp_rw [hk]
  rw [Finset.univ_eq_attach, Finset.sup_attach (descendantsAtDepth Q 134)
    (fun U => ENNReal.ofReal (lemmaVInverseHistory U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (oldCutoffSkewCoefficient m U ω)) ((3 : ℝ) ^ (1 / 4 : ℝ))))]


/-- The bank's split of the actual history maximum `B` over the physical
population of side-`(m-5)` cells. -/
theorem bank_B (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m, nativeInductionState M h n) (Q : TriadicCube 2)
    (hQ : Q.scale = m + 129) :
    eLpNorm (fun ω => bhist M m Q 134 ω) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (14103 / 10000) ∧
      eLpNorm (fun ω => max (bhist M m Q 134 ω - 14103 / 10000) 0) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (5 / 10 ^ 24) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let I := descendantsAtDepth Q 89
  let fam : TriadicCube 2 → Finset (TriadicCube 2) := fun i => descendantsAtDepth i 45
  let w := bankPartialInsertionWeights m 1 0
  have hI : I.card ≤ 9 ^ 89 := by
    simp only [I]; rw [descendantsAtDepth_card]; norm_num
  have hw : ∀ k ∈ Finset.Ioc m (m + 40), 0 ≤ w k ∧ w k ≤ 1 := fun k _ =>
    bank_partial_insertion_weights_bounds m 1 0 (by norm_num) k
  have hscale : ∀ i ∈ I, ∀ U ∈ fam i, U.scale ≤ m ∧ m - U.scale ≤ 5 := by
    intro i hi U hU
    have h1 := scale_eq_sub_of_mem_descendantsAtDepth hU
    have h2 := scale_eq_sub_of_mem_descendantsAtDepth hi
    have : U.scale = m - 5 := by
      rw [h1, h2, hQ]; push_cast; ring
    rw [this]; constructor <;> omega
  have hcard : ∀ i ∈ I, (fam i).card ≤ 6 * 9 ^ 45 := by
    intro i _
    simp only [fam]; rw [descendantsAtDepth_card]; norm_num
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hγ m hpast).1
  obtain ⟨hfamily, hrem, hhist⟩ := global_bank M h hM hγ I fam hI m (m + 40) (by omega) w hw
    hscale hcard hpast hmean
  have hBnn (x : Cutoff.CutoffSample 2) : 0 ≤ bhist M m Q 134 x :=
    smooth_feedback_source_history_maximum_nonneg Q 134 M.nu (Annealed.sigmaBar M m : ℝ) _
  have hB (x : Cutoff.CutoffSample 2) : ‖bhist M m Q 134 x‖ₑ =
      inverseBankGroupedHistory I fam M m (m + 40) w x := by
    rw [← Bhist_eq_grouped M m Q x, Real.enorm_eq_ofReal (hBnn x)]
  have hGm : Measurable (inverseBankGroupedHistory I fam M m (m + 40) w) :=
    history_finite_max_measurable _ _ (fun i => history_finite_max_measurable _ _
      (fun U => bank_root_inverse_history_measurable U.1 M m (m + 40) w))
  have hBm : Measurable (fun x => bhist M m Q 134 x) := by
    have : (fun x => bhist M m Q 134 x) =
        fun x => (inverseBankGroupedHistory I fam M m (m + 40) w x).toReal := by
      funext x
      rw [← Bhist_eq_grouped M m Q x, ENNReal.toReal_ofReal (hBnn x)]
    rw [this]
    exact hGm.ennreal_toReal
  refine ⟨?_, ?_⟩
  · refine le_trans (le_of_eq ?_) hhist
    exact eLpNorm_congr_enorm_ae hBm.aestronglyMeasurable hGm.aestronglyMeasurable
      (Filter.Eventually.of_forall hB)
  · have hcap : (inverseBankCap .globalInverse : ℝ) = 14103 / 10000 := by
      norm_num [inverseBankCap]
    have hae : ∀ᵐ x ∂μ, ∀ i ∈ I, bankFiniteRootHistoryMax (fam i) M m (m + 40) w x ≤
        ENNReal.ofReal (14103 / 10000) + ENNReal.ofReal
          (inverseBankPopulationRemainder .globalInverse (fam i) M m (m + 40) w x) := by
      refine (Filter.eventually_all_finset I).2 (fun i hi => ?_)
      filter_upwards [(hfamily i hi).history_le] with x hx
      rwa [hcap] at hx
    have hmaj : ∀ᵐ x ∂μ, ENNReal.ofReal (max (bhist M m Q 134 x - 14103 / 10000) 0) ≤
        inverseBankGroupedRemainder .globalInverse I fam M m (m + 40) w x := by
      filter_upwards [hae] with x hx
      have h1 : ENNReal.ofReal (max (bhist M m Q 134 x - 14103 / 10000) 0) ≤
          ENNReal.ofReal (bhist M m Q 134 x) - ENNReal.ofReal (14103 / 10000) := by
        rcases le_total (bhist M m Q 134 x) (14103 / 10000) with h | h
        · rw [max_eq_right (by linarith)]; simp
        · rw [max_eq_left (by linarith), ← ENNReal.ofReal_sub _ (by norm_num)]
      refine h1.trans ?_
      rw [Bhist_eq_grouped M m Q x, tsub_le_iff_left]
      unfold inverseBankGroupedHistory inverseBankGroupedRemainder historyFiniteMax
      refine Finset.sup_le (fun i hi => (hx i hi).trans ?_)
      exact add_le_add le_rfl (Finset.le_sup (f := fun i => ENNReal.ofReal
        (inverseBankPopulationRemainder .globalInverse (fam i) M m (m + 40) w x)) hi)
    have hmeas : Measurable (fun x => max (bhist M m Q 134 x - 14103 / 10000) 0) :=
      (hBm.sub_const _).max measurable_const
    refine le_trans ?_ hrem
    refine eLpNorm_mono_enorm_ae hmeas.aestronglyMeasurable ?_
    filter_upwards [hmaj] with x hx
    rw [Real.enorm_eq_ofReal (le_max_right _ _)]
    exact hx


end

end ASDExplicitGamma.Scalar
