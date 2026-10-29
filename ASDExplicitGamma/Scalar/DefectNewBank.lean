module

public import ASDExplicitGamma.Scalar.SmoothFeedbackBank
public import ASDExplicitGamma.Scalar.PairedTwoSlotBank

/-! The NEW global inverse bank (full insertion `t = 1`, frame `σ̄_m`) over the depth-134 cells
of `Q_{m+129}`: the history maximum `B*` satisfies the bank split `B* ≤ β + R*` with
`‖B*‖₁₂₈ ≤ β`, `‖R*‖₁₂₈ ≤ ε`. -/
@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native ASDExplicitGamma.Inverse ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3
open scoped BigOperators ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

/-- The NEW history maximum over the depth-134 cells of `Q`, in the frame `σ̄_m`. -/
def bnew (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  Book.Ch02.finsetSupReal (descendantsAtDepth Q 134) (fun U =>
    (Annealed.sigmaBar M m : ℝ) * lemmaVInverseHistory U
      (Model.partialInsertedCoefficient M m 1 ω).toFun ((3 : ℝ) ^ (1 / 4 : ℝ)))

theorem bnew_nonneg (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) :
    0 ≤ bnew M m Q ω := by
  unfold bnew
  apply Book.Ch02.finsetSupReal_nonneg
  intro U _
  exact mul_nonneg (Annealed.sigmaBar M m).property.le
    (lemmaVInverseHistory_nonneg U _ (Real.one_lt_rpow (by norm_num) (by norm_num)))

theorem le_finsetSupReal'' {α : Type*} (s : Finset α) (f : α → ℝ) {x : α} (hx : x ∈ s) :
    f x ≤ Book.Ch02.finsetSupReal s f := by
  classical
  have hbdd : BddAbove (f '' (↑s : Set α)) := ((Set.toFinite _).image f).bddAbove
  unfold Book.Ch02.finsetSupReal
  exact le_csSup hbdd ⟨x, hx, rfl⟩

/-- The sharp cell-history bound feeding item 3: every depth-134 cell's frame history of the
literal NEW coefficient is at most `B*`. -/
theorem Bnew_cell_bound (M : ABKModel 2) (ell m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (K : Set (Vec 2)) [CompactSpace K]
    (hQ : closure (openCubeSet Q) ⊆ K) (hK : K ⊆ openCubeSet (originCube 2 ell)) :
    ∀ U ∈ descendantsAtDepth Q 134, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (physicalResponseRestriction Q hQ (modelInsertedScalar K m 1 ω)))
      ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ bnew M m Q ω := by
  intro U hU
  rw [partial_insertion_frame_history_eq_cell Q U 134 hU M ell m ω _
    (Annealed.sigmaBar M m).property K hQ hK]
  exact le_finsetSupReal'' (descendantsAtDepth Q 134) (fun U =>
    (Annealed.sigmaBar M m : ℝ) * lemmaVInverseHistory U
      (Model.partialInsertedCoefficient M m 1 ω).toFun ((3 : ℝ) ^ (1 / 4 : ℝ))) hU

/-- The actual NEW history maximum is the bank's grouped history at `t = 1`. -/
theorem Bnew_eq_grouped (M : ABKModel 2) (ell m : ℤ) (Q : TriadicCube 2)
    (hQ : openCubeSet Q ⊆ openCubeSet (originCube 2 ell)) (ω : Cutoff.CutoffSample 2) :
    ENNReal.ofReal (bnew M m Q ω) =
      inverseBankGroupedHistory (descendantsAtDepth Q 89)
        (fun i => descendantsAtDepth i 45) M m (m + 40)
        (bankPartialInsertionWeights m 1 1) ω := by
  classical
  have hD : descendantsAtDepth Q 134 =
      (descendantsAtDepth Q 89).biUnion (fun i => descendantsAtDepth i 45) :=
    descendants_split Q 89 45
  have hfam (i : TriadicCube 2) :
      bankFiniteRootHistoryMax (descendantsAtDepth i 45) M m (m + 40)
        (bankPartialInsertionWeights m 1 1) ω =
      (descendantsAtDepth i 45).sup
        (fun U => bankRootInverseHistory U M m (m + 40)
          (bankPartialInsertionWeights m 1 1) ω) := by
    unfold bankFiniteRootHistoryMax historyFiniteMax
    change (descendantsAtDepth i 45).attach.sup
      (fun U => bankRootInverseHistory U.1 M m (m + 40)
        (bankPartialInsertionWeights m 1 1) ω) = _
    exact Finset.sup_attach (descendantsAtDepth i 45)
      (fun U => bankRootInverseHistory U M m (m + 40)
        (bankPartialInsertionWeights m 1 1) ω)
  have hbank (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q 134) :
      bankRootInverseHistory U M m (m + 40) (bankPartialInsertionWeights m 1 1) ω =
        ENNReal.ofReal ((Annealed.sigmaBar M m : ℝ) * lemmaVInverseHistory U
          (Model.partialInsertedCoefficient M m 1 ω).toFun ((3 : ℝ) ^ (1 / 4 : ℝ))) := by
    have ha : attenuatedCoefficient M m (m + 40) (bankPartialInsertionWeights m 1 1) ω =
        (Model.partialInsertedCoefficient M m 1 ω).toFun := by
      have := bank_one_pass_partial_coefficient M m 1 (by norm_num) 1 ω
      simpa using this
    have hUopen : openCubeSet U ⊆ openCubeSet Q := openCubeSet_subset_of_mem_descendantsAtDepth hU
    have hEll := Model.partialInsertedCoefficient_isEllipticFieldOn
      M ell m ω (t := 1) ⟨by norm_num, by norm_num⟩
      (measurableSet_openCubeSet U) (fun _ hx => hQ (hUopen hx))
    exact bank_root_history_physical U M m (m + 40) (bankPartialInsertionWeights m 1 1) ω _ ha hEll
  unfold inverseBankGroupedHistory historyFiniteMax
  have hfam' : ∀ i : TriadicCube 2, bankFiniteRootHistoryMax (descendantsAtDepth i 45) M m (m + 40)
        (bankPartialInsertionWeights m 1 1) ω = bankFiniteRootHistoryMax (descendantsAtDepth i 45)
        M m (m + 40) (bankPartialInsertionWeights m 1 1) ω := fun _ => rfl
  simp_rw [hfam]
  have hne : (descendantsAtDepth Q 134).Nonempty := by
    have : (descendantsAtDepth Q 134).card ≠ 0 := by
      rw [descendantsAtDepth_card]; positivity
    exact Finset.card_pos.mp (Nat.pos_of_ne_zero this)
  unfold bnew
  rw [ofReal_finsetSupReal _ hne _ (fun U _ => mul_nonneg (Annealed.sigmaBar M m).property.le
    (lemmaVInverseHistory_nonneg U _ (Real.one_lt_rpow (by norm_num) (by norm_num))))]
  rw [hD, Finset.sup_biUnion]
  refine Finset.sup_congr rfl fun i hi => ?_
  refine Finset.sup_congr rfl fun U hU => ?_
  rw [hbank U (by rw [hD]; exact Finset.mem_biUnion.mpr ⟨i, hi, hU⟩)]

theorem bnew_measurable (M : ABKModel 2) (ell m : ℤ) (Q : TriadicCube 2)
    (hQell : openCubeSet Q ⊆ openCubeSet (originCube 2 ell)) :
    Measurable (fun ω => bnew M m Q ω) := by
  classical
  have hGm : Measurable (inverseBankGroupedHistory (descendantsAtDepth Q 89)
      (fun i => descendantsAtDepth i 45) M m (m + 40) (bankPartialInsertionWeights m 1 1)) :=
    history_finite_max_measurable _ _ (fun i => history_finite_max_measurable _ _
      (fun U => bank_root_inverse_history_measurable U.1 M m (m + 40) _))
  have : (fun x => bnew M m Q x) = fun x => (inverseBankGroupedHistory (descendantsAtDepth Q 89)
      (fun i => descendantsAtDepth i 45) M m (m + 40) (bankPartialInsertionWeights m 1 1) x).toReal := by
    funext x
    rw [← Bnew_eq_grouped M ell m Q hQell x, ENNReal.toReal_ofReal (bnew_nonneg M m Q x)]
  rw [this]
  exact hGm.ennreal_toReal

/-- The NEW bank's split of `B*` over the depth-134 cells of `Q_{m+129}`. -/
theorem bank_Bnew (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m, nativeInductionState M h n) (Q : TriadicCube 2)
    (hQ : Q.scale = m + 129) (ell : ℤ)
    (hQell : openCubeSet Q ⊆ openCubeSet (originCube 2 ell)) :
    eLpNorm (fun ω => bnew M m Q ω) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (14103 / 10000) ∧
      eLpNorm (fun ω => max (bnew M m Q ω - 14103 / 10000) 0) 128
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (5 / 10 ^ 24) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let I := descendantsAtDepth Q 89
  let fam : TriadicCube 2 → Finset (TriadicCube 2) := fun i => descendantsAtDepth i 45
  let w := bankPartialInsertionWeights m 1 1
  have hI : I.card ≤ 9 ^ 89 := by
    simp only [I]; rw [descendantsAtDepth_card]; norm_num
  have hw : ∀ k ∈ Finset.Ioc m (m + 40), 0 ≤ w k ∧ w k ≤ 1 := fun k _ =>
    bank_partial_insertion_weights_bounds m 1 1 (by norm_num) k
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
  have hBnn (x : Cutoff.CutoffSample 2) : 0 ≤ bnew M m Q x :=
    bnew_nonneg M m Q x
  have hB (x : Cutoff.CutoffSample 2) : ‖bnew M m Q x‖ₑ =
      inverseBankGroupedHistory I fam M m (m + 40) w x := by
    rw [← Bnew_eq_grouped M ell m Q hQell x, Real.enorm_eq_ofReal (hBnn x)]
  have hGm : Measurable (inverseBankGroupedHistory I fam M m (m + 40) w) :=
    history_finite_max_measurable _ _ (fun i => history_finite_max_measurable _ _
      (fun U => bank_root_inverse_history_measurable U.1 M m (m + 40) w))
  have hBm : Measurable (fun x => bnew M m Q x) := by
    have : (fun x => bnew M m Q x) =
        fun x => (inverseBankGroupedHistory I fam M m (m + 40) w x).toReal := by
      funext x
      rw [← Bnew_eq_grouped M ell m Q hQell x, ENNReal.toReal_ofReal (hBnn x)]
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
    have hmaj : ∀ᵐ x ∂μ, ENNReal.ofReal (max (bnew M m Q x - 14103 / 10000) 0) ≤
        inverseBankGroupedRemainder .globalInverse I fam M m (m + 40) w x := by
      filter_upwards [hae] with x hx
      have h1 : ENNReal.ofReal (max (bnew M m Q x - 14103 / 10000) 0) ≤
          ENNReal.ofReal (bnew M m Q x) - ENNReal.ofReal (14103 / 10000) := by
        rcases le_total (bnew M m Q x) (14103 / 10000) with h | h
        · rw [max_eq_right (by linarith)]; simp
        · rw [max_eq_left (by linarith), ← ENNReal.ofReal_sub _ (by norm_num)]
      refine h1.trans ?_
      rw [Bnew_eq_grouped M ell m Q hQell x, tsub_le_iff_left]
      unfold inverseBankGroupedHistory inverseBankGroupedRemainder historyFiniteMax
      refine Finset.sup_le (fun i hi => (hx i hi).trans ?_)
      exact add_le_add le_rfl (Finset.le_sup (f := fun i => ENNReal.ofReal
        (inverseBankPopulationRemainder .globalInverse (fam i) M m (m + 40) w x)) hi)
    have hmeas : Measurable (fun x => max (bnew M m Q x - 14103 / 10000) 0) :=
      (hBm.sub_const _).max measurable_const
    refine le_trans ?_ hrem
    refine eLpNorm_mono_enorm_ae hmeas.aestronglyMeasurable ?_
    filter_upwards [hmaj] with x hx
    rw [Real.enorm_eq_ofReal (le_max_right _ _)]
    exact hx


end

end ASDExplicitGamma.Scalar
