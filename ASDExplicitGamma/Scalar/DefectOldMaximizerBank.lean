module

public import ASDExplicitGamma.Scalar.SmoothFeedbackBank
public import ASDExplicitGamma.Inverse.BankDepthBlocks
public import ASDExplicitGamma.Inverse.BankOnePassMeanActual
public import ASDExplicitGamma.Inverse.PositivePopulation

/-! The grouped OLD local depth-block bank on the scalar observer
`Q = Q_{m+129}`: the depth-`134+j` inverse maximum against the baseline plus one
nonnegative `L^128` remainder (the 9^89 groups of `Q_{m+40}`-cells pay the
factor five). -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory Homogenization Response Triadic Variational Native Inverse
open Algsuperdiff.Section3
open scoped ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth
noncomputable section

/-- The frame-normalised depth-`k` inverse maximum of `Q` for the OLD skew coefficient. -/
def depthMax (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (k : ℕ) : ℝ :=
  lemmaVInverseDepthMax Q (responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω)) k

/-- Frame factorisation of the depth maximum (as for the history in `cell_inverse_history_frame`). -/
theorem depthMax_frame (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) :
    depthMax M m U ω j =
      (Annealed.sigmaBar M m : ℝ) *
        lemmaVInverseDepthMax U (Cutoff.coefficientCutoff M.nu m ω).toFun j := by
  let σ : ℝ := Annealed.sigmaBar M m
  have hσ : 0 < σ := (Annealed.sigmaBar M m).property
  let phys := (Cutoff.coefficientCutoff M.nu m ω).toFun
  set aU := responseFramePlanarCoefficientField M.nu σ (oldCutoffSkewCoefficient m U ω) with haU
  have hEllPhys := Cutoff.isEllipticFieldOn_coefficientCutoff_cube M m ω U
  have hEllA := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet U) M.nu σ M.nu_pos hσ (oldCutoffSkewCoefficient m U ω)
  have hmatrix (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth U j) :
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
  unfold depthMax
  rw [← Scalar.inverse_history_framed_depth_max U phys hEllPhys σ hσ j]
  unfold lemmaVInverseDepthMax
  apply Book.Ch02.finsetSupReal_congr
  intro R hR
  have hmatrixR := hmatrix R hR
  have hlow := congrArg (fun A : BlockMat 2 => A.lowerRight) hmatrixR
  apply congrArg Book.Ch02.matrixNorm
  rw [Scalar.inverse_history_lowerRight R aU
    (hEllA.mono (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR))]
  rw [hlow]
  rfl


/-- The grouped depth-`j` local bank at the scalar observer. -/
theorem depth_bank (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m, nativeInductionState M h n) (Q : TriadicCube 2)
    (hQ : Q.scale = m + 129) (j : ℕ) :
    ∃ ε : Cutoff.CutoffSample 2 → ℝ, Measurable ε ∧ (∀ ω, 0 ≤ ε ω) ∧
      eLpNorm ε 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal (5 * inverseBankDepthReserve .localInverse M j) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        depthMax M m Q ω (134 + j) ≤
          (3683 / 2500 : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) + ε ω) ∧
      (∀ ω, ε ω ≤ depthMax M m Q ω (134 + j)) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let σ : ℝ := Annealed.sigmaBar M m
  have hσ : 0 < σ := (Annealed.sigmaBar M m).property
  let I := descendantsAtDepth Q 89
  let w := bankPartialInsertionWeights m 1 0
  let fam : TriadicCube 2 → Finset (TriadicCube 2) := fun i => descendantsAtDepth i (45 + j)
  let rem : TriadicCube 2 → Cutoff.CutoffSample 2 → ℝ := fun i ω =>
    inverseBankDepthBlockRemainder .localInverse (fam i) M m (m + 40) w j ω
  have hI : I.card ≤ 9 ^ 89 := by
    simp only [I]; rw [descendantsAtDepth_card]; norm_num
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hγ m hpast).2
  have hiScale (i : TriadicCube 2) (hi : i ∈ I) : i.scale = m + 40 := by
    have := scale_eq_sub_of_mem_descendantsAtDepth hi
    rw [this, hQ]; push_cast; ring
  have hbank (i : ↥I) :=
    inverse_bank_depth_block M h hM hγ .localInverse (fam i.1) m (m + 40) (by omega) w
      (fun k hk => bank_partial_insertion_weights_bounds m 1 0 (by norm_num) k) j
      (by
        intro R hR
        have h1 := scale_eq_sub_of_mem_descendantsAtDepth hR
        rw [h1, hiScale i.1 i.2]; push_cast; constructor <;> omega)
      (by
        simp only [fam]; rw [descendantsAtDepth_card]
        have : (9:ℕ) ^ (45 + j) ≤ 6 * 9 ^ (45 + j) := by omega
        exact this)
      (fun n hn => hpast n hn) hmean
  let E : Cutoff.CutoffSample 2 → ℝ≥0∞ :=
    historyFiniteMax I.attach (fun i ω => ENNReal.ofReal (rem i.1 ω))
  have hEmeas : Measurable E :=
    history_finite_max_measurable _ _ (fun i =>
      ENNReal.measurable_ofReal.comp (hbank i).remainder_measurable)
  have hEfin (ω : Cutoff.CutoffSample 2) : E ω < ∞ := by
    change I.attach.sup (fun i => ENNReal.ofReal (rem i.1 ω)) < ∞
    exact (Finset.sup_lt_iff (by simp)).mpr (fun i _ => ENNReal.ofReal_lt_top)
  let ε : Cutoff.CutoffSample 2 → ℝ := fun ω => (E ω).toReal
  have hεnn (ω) : 0 ≤ ε ω := ENNReal.toReal_nonneg
  have hremLe (i : ↥I) (ω) : rem i.1 ω ≤ ε ω := by
    have : ENNReal.ofReal (rem i.1 ω) ≤ E ω :=
      Finset.le_sup (f := fun i : ↥I => ENNReal.ofReal (rem i.1 ω)) (Finset.mem_attach _ i)
    exact (ENNReal.ofReal_le_iff_le_toReal (hEfin ω).ne).mp this
  have hεmeas : Measurable ε := ENNReal.measurable_toReal.comp hEmeas
  have hha : ∀ ω : Cutoff.CutoffSample 2,
      attenuatedCoefficient M m (m + 40) w ω =
        (Cutoff.coefficientCutoff M.nu m ω).toFun := by
    intro ω
    have := bank_one_pass_partial_coefficient M m 1 (by norm_num) 0 ω
    rw [this]
    simpa using partialInserted_zero M m ω
  have hY (i : ↥I) (ω : Cutoff.CutoffSample 2) :
      bankFiniteRootResponseMax (fam i.1) M m (m + 40) w ω =
        ENNReal.ofReal (σ * lemmaVInverseDepthMax i.1
          (Cutoff.coefficientCutoff M.nu m ω).toFun (45 + j)) :=
    bank_depth_max_physical i.1 M m (m + 40) w ω _ (hha ω)
      (Cutoff.isEllipticFieldOn_coefficientCutoff_cube M m ω i.1) (45 + j)
  have hmem (i : ↥I) (R : TriadicCube 2) (hR : R ∈ fam i.1) :
      R ∈ descendantsAtDepth Q (134 + j) := by
    have := mem_descendantsAtDepth_add i.2 hR
    rwa [show 89 + (45 + j) = 134 + j by omega] at this
  have hcover (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q (134 + j)) :
      ∃ i : ↥I, R ∈ fam i.1 := by
    have hs := descendants_split Q 89 (45 + j)
    rw [show 89 + (45 + j) = 134 + j by omega] at hs
    rw [hs, Finset.mem_biUnion] at hR
    obtain ⟨i, hi, hRi⟩ := hR
    exact ⟨⟨i, hi⟩, hRi⟩
  refine ⟨ε, hεmeas, hεnn, ?_, ?_, ?_⟩
  · have h1 : eLpNorm ε 128 μ ≤ eLpNorm E 128 μ :=
      eLpNorm_mono_enorm_ae hεmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by
        simpa [ε, Real.enorm_eq_ofReal ENNReal.toReal_nonneg] using
          (ENNReal.ofReal_toReal_le (a := E ω))))
    have h2 := positive_finite_max_L128 μ I.attach (fun i ω => ENNReal.ofReal (rem i.1 ω))
      (fun i => ENNReal.measurable_ofReal.comp (hbank i).remainder_measurable)
      (ENNReal.ofReal (inverseBankDepthReserve .localInverse M j)) (fun i _ => by
        change eLpNorm (ENNReal.ofReal ∘ rem i.1) 128 μ ≤ _
        rw [eLpNorm_ofReal (rem i.1) (Filter.Eventually.of_forall (hbank i).remainder_nonneg)]
        exact (hbank i).remainder_L128)
    have h3 : (I.attach.card : ℝ≥0∞) ^ (1 / 128 : ℝ) ≤ 5 := by
      rw [Finset.card_attach]; exact bank_scalar_grouping_payment I.card hI
    refine h1.trans (h2.trans ?_)
    calc _ ≤ 5 * ENNReal.ofReal (inverseBankDepthReserve .localInverse M j) :=
          mul_le_mul_of_nonneg_right h3 bot_le
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]; norm_num
  · -- pointwise split
    have hae : ∀ᵐ ω ∂μ, ∀ i : ↥I,
        bankFiniteRootResponseMax (fam i.1) M m (m + 40) w ω ≤
          ENNReal.ofReal ((inverseBankCap .localInverse : ℝ) * bankDepthFrame M j) +
            ENNReal.ofReal (rem i.1 ω) :=
      ae_all_iff.mpr (fun i => (hbank i).block_le)
    filter_upwards [hae] with ω hω
    rw [depthMax_frame]
    have hcap0 : (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j =
        (3683 / 2500 : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) := by
      simp [inverseBankCap, bankDepthFrame]
    rw [← hcap0]
    have hcapnn : 0 ≤ (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j := by
      rw [hcap0]; positivity
    have hblock (i : ↥I) : σ * lemmaVInverseDepthMax i.1
        (Cutoff.coefficientCutoff M.nu m ω).toFun (45 + j) ≤
          (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j + ε ω := by
      have h1 := hω i
      have hr0 : 0 ≤ rem i.1 ω := (hbank i).remainder_nonneg ω
      rw [hY i ω, ← ENNReal.ofReal_add hcapnn hr0] at h1
      have h2 := (ENNReal.ofReal_le_ofReal_iff (add_nonneg hcapnn hr0)).mp h1
      linarith [hremLe i ω]
    have hDQ : lemmaVInverseDepthMax Q (Cutoff.coefficientCutoff M.nu m ω).toFun (134 + j) ≤
        ((inverseBankCap .localInverse : ℝ) * bankDepthFrame M j + ε ω) / σ := by
      unfold lemmaVInverseDepthMax
      apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty Q _)
      intro R hR
      obtain ⟨i, hRi⟩ := hcover R hR
      have hgi := Algsuperdiff.Section3.Provider.ErrorComparison.le_finsetSupReal
        (fam i.1) (fun R => Book.Ch02.matrixNorm
          (sigmaStarInvCoarse (openCubeSet R) (Cutoff.coefficientCutoff M.nu m ω).toFun)) hRi
      refine hgi.trans ?_
      rw [le_div_iff₀ hσ]
      have := hblock i
      change lemmaVInverseDepthMax i.1 (Cutoff.coefficientCutoff M.nu m ω).toFun (45 + j) * σ ≤ _
      linarith
    have := mul_le_mul_of_nonneg_left hDQ hσ.le
    rwa [mul_div_cancel₀ _ hσ.ne'] at this
  · intro ω
    rw [depthMax_frame]
    have hnn := inverse_bank_depth_nonneg .localInverse M j
    have hrem (i : ↥I) : rem i.1 ω ≤ σ * lemmaVInverseDepthMax Q
        (Cutoff.coefficientCutoff M.nu m ω).toFun (134 + j) := by
      have hDi : lemmaVInverseDepthMax i.1 (Cutoff.coefficientCutoff M.nu m ω).toFun (45 + j) ≤
          lemmaVInverseDepthMax Q (Cutoff.coefficientCutoff M.nu m ω).toFun (134 + j) := by
        unfold lemmaVInverseDepthMax
        apply Book.Ch02.finsetSupReal_le _ (descendantsAtDepth_nonempty _ _)
        intro R hR
        exact Algsuperdiff.Section3.Provider.ErrorComparison.le_finsetSupReal
          (descendantsAtDepth Q (134 + j)) (fun R => Book.Ch02.matrixNorm
            (sigmaStarInvCoarse (openCubeSet R) (Cutoff.coefficientCutoff M.nu m ω).toFun))
          (hmem i R hR)
      have hD0 : 0 ≤ lemmaVInverseDepthMax i.1 (Cutoff.coefficientCutoff M.nu m ω).toFun (45 + j) :=
        lemmaVInverseDepthMax_nonneg _ _ _
      have hyeq : (bankFiniteRootResponseMax (fam i.1) M m (m + 40) w ω).toReal =
          σ * lemmaVInverseDepthMax i.1 (Cutoff.coefficientCutoff M.nu m ω).toFun (45 + j) := by
        rw [hY i ω, ENNReal.toReal_ofReal (mul_nonneg hσ.le hD0)]
      have hrem' : rem i.1 ω ≤ σ * lemmaVInverseDepthMax i.1
          (Cutoff.coefficientCutoff M.nu m ω).toFun (45 + j) := by
        change positiveSplitRemainder
          (bankFiniteRootResponseMax (fam i.1) M m (m + 40) w ω).toReal _ _ ≤ _
        rw [hyeq]
        unfold positiveSplitRemainder
        exact max_le_iff.mpr ⟨mul_nonneg hσ.le hD0, by linarith [hnn.1, hnn.2.2]⟩
      exact hrem'.trans (mul_le_mul_of_nonneg_left hDi hσ.le)
    have hE : E ω ≤ ENNReal.ofReal (σ * lemmaVInverseDepthMax Q
        (Cutoff.coefficientCutoff M.nu m ω).toFun (134 + j)) := by
      change I.attach.sup (fun i => ENNReal.ofReal (rem i.1 ω)) ≤ _
      exact Finset.sup_le (fun i _ => ENNReal.ofReal_le_ofReal (hrem i))
    exact ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg hσ.le (lemmaVInverseDepthMax_nonneg _ _ _)) hE

theorem depthMax_measurable (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (k : ℕ) :
    Measurable (fun ω => depthMax M m Q ω k) := by
  classical
  let w := bankPartialInsertionWeights m 1 0
  have hY : Measurable (bankFiniteRootResponseMax (descendantsAtDepth Q k) M m (m + 40) w) :=
    history_finite_max_measurable _ _ (fun R => ENNReal.measurable_ofReal.comp
      (root_inverse_response_measurable M m (m + 40) w R.1))
  have hha : ∀ ω : Cutoff.CutoffSample 2,
      attenuatedCoefficient M m (m + 40) w ω =
        (Cutoff.coefficientCutoff M.nu m ω).toFun := by
    intro ω
    have := bank_one_pass_partial_coefficient M m 1 (by norm_num) 0 ω
    rw [this]
    simpa using partialInserted_zero M m ω
  have heq : (fun ω => depthMax M m Q ω k) = fun ω =>
      (bankFiniteRootResponseMax (descendantsAtDepth Q k) M m (m + 40) w ω).toReal := by
    funext ω
    rw [bank_depth_max_physical Q M m (m + 40) w ω _ (hha ω)
      (Cutoff.isEllipticFieldOn_coefficientCutoff_cube M m ω Q) k,
      ENNReal.toReal_ofReal (mul_nonneg (Annealed.sigmaBar M m).property.le
        (lemmaVInverseDepthMax_nonneg _ _ _)), depthMax_frame]
  rw [heq]
  exact ENNReal.measurable_toReal.comp hY

end
end ASDExplicitGamma.Scalar
