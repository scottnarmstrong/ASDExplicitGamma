module

public import ASDExplicitGamma.Inverse.BankPointwiseMoment
public import ASDExplicitGamma.Inverse.HistoryLpSeries

/-! Order-256 finite population payments for the literal inverse response. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal

noncomputable def bankHistoryAlpha : ℝ≥0∞ := ENNReal.ofReal ((3:ℝ)^(-(1/4:ℝ)))

noncomputable def bankHistoryPrefactor : ℝ≥0∞ :=
  ENNReal.ofReal (1-(3:ℝ)^(-(1/4:ℝ)))

/-- Complete normalized inverse history in the fixed true frame. -/
noncomputable def bankRootInverseHistory (Q : TriadicCube 2)
    (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  bankHistoryPrefactor * ∑' j : ℕ,
    bankHistoryAlpha^j * bankFiniteRootResponseMax (descendantsAtDepth Q j)
      M m J weights ω

noncomputable def bankRootDepthBaseline (M : ABKModel 2) (Q : TriadicCube 2)
    (m : ℤ) (r : RootRow) (j : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) *
    (ENNReal.ofReal (rootLi M.gamma r) *
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27))))

noncomputable def bankRootInverseBaselineHistory (Q : TriadicCube 2)
    (M : ABKModel 2) (m : ℤ) (r : RootRow) : ℝ≥0∞ :=
  bankHistoryPrefactor * ∑' j : ℕ,
    bankHistoryAlpha^j * bankRootDepthBaseline M Q m r j

theorem bank_depth_root_response_measurable (Q : TriadicCube 2) (j : ℕ)
    (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ) :
    Measurable (bankFiniteRootResponseMax (descendantsAtDepth Q j) M m J weights) := by
  exact history_finite_max_measurable _ _ (fun V =>
    ENNReal.continuous_ofReal.measurable.comp
      (root_inverse_response_measurable M m J weights V.1))

/-- Split the selected physical clock into its deterministic first twelve
heights and the actual positive selected tail. -/
theorem bank_selected_clock_le_base_add_tail (M : ABKModel 2)
    (Q : TriadicCube 2) (r : RootRow) (ω : Cutoff.CutoffSample 2) :
    selectedHeightClock M.gamma (rootSelectedHeight M Q r) ω ≤
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27))) +
        selectedRootClockTail M.gamma (rootH0 r)
          (rootSelectedHeight M Q r) ω := by
  let H := rootSelectedHeight M Q r
  by_cases hlarge : rootH0 r + 11 < H ω
  · rw [selected_root_clock_tail_eq M.gamma (rootH0 r) H ω]
    simp only [hlarge, ite_true]
    exact le_add_of_nonneg_left (by positivity)
  · have hsmall : H ω ≤ rootH0 r + 11 := by omega
    have hsmall' : (H ω:ℝ) - 38 ≤ (rootH0 r:ℝ) - 27 := by
      have hsmallR : (H ω:ℝ) ≤ (rootH0 r:ℝ) + 11 := by exact_mod_cast hsmall
      linarith only [hsmallR]
    have hgamma : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
    have hexp : 2*M.gamma*((H ω:ℝ)-38) ≤ 2*M.gamma*((rootH0 r:ℝ)-27) :=
      mul_le_mul_of_nonneg_left hsmall' (by positivity : 0 ≤ 2*M.gamma)
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 3) hexp
    rw [selected_root_clock_tail_eq M.gamma (rootH0 r) H ω]
    simp only [hlarge, ite_false, add_zero]
    change ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((H ω:ℝ)-38))) ≤
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27)))
    exact ENNReal.ofReal_le_ofReal hpow

theorem bank_root_Li_nonneg (γ : ℝ) (r : RootRow) : 0 ≤ rootLi γ r := by
  have hq := (root_row_density_inputs r).1
  have hT : 0 ≤ rootMomentCutoff r := by cases r <;> norm_num [rootMomentCutoff]
  have hM2 := density_moment_budget_nonneg (rootQ r) hq 2
    (rootMomentCutoff r) hT
  have hmean : 0 ≤ rootMeanCap r := by cases r <;> norm_num [rootMeanCap]
  have hC : 0 ≤ 3*(planarGradientCharge 40+1) := by
    unfold planarGradientCharge
    positivity
  have hτ : 0 ≤ rootTau r := by cases r <;> norm_num [rootTau]
  have hEnvelope : 0 ≤ rootResponseEnvelope (6*rootTau r) := by
    unfold rootResponseEnvelope
    positivity
  have hInner : 0 ≤ rootMeanCap r + 3*(planarGradientCharge 40+1)*
      rootResponseEnvelope (6*rootTau r)*densityMomentBudget (rootQ r) 2
        (rootMomentCutoff r) :=
    add_nonneg hmean (mul_nonneg (mul_nonneg hC hEnvelope) hM2)
  have hEd : 0 ≤ rootEdelta r := by unfold rootEdelta; positivity
  have hLayer : 0 ≤ rootLayerSum (2*γ) := by
    unfold rootLayerSum
    apply tsum_nonneg
    intro n
    exact mul_nonneg (bankLayerWeight_nonneg n) (by positivity)
  unfold rootLi
  exact mul_nonneg (mul_nonneg hEd hInner) hLayer

noncomputable def bankRootSelectedRemainder (M : ABKModel 2)
    (Q : TriadicCube 2) (r : RootRow) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ENNReal.ofReal (rootLi M.gamma r) *
    selectedRootClockTail M.gamma (rootH0 r) (rootSelectedHeight M Q r) ω +
      positiveRootError M Q r ω

noncomputable def bankRootFrameFactor (M : ABKModel 2) (Q : TriadicCube 2)
    (m : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-Q.scale+1:ℤ):ℝ)|))

noncomputable def bankRootResponseBaseline (M : ABKModel 2) (Q : TriadicCube 2)
    (m : ℤ) (r : RootRow) : ℝ≥0∞ :=
  bankRootFrameFactor M Q m * (ENNReal.ofReal (rootLi M.gamma r) *
    ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27))))

noncomputable def bankRootScaledSelectedRemainder (M : ABKModel 2)
    (Q : TriadicCube 2) (m : ℤ) (r : RootRow)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  bankRootFrameFactor M Q m * bankRootSelectedRemainder M Q r ω

noncomputable def bankFiniteRootRemainderMax (s : Finset (TriadicCube 2))
    (M : ABKModel 2) (m : ℤ) (r : RootRow)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  historyFiniteMax (Finset.univ : Finset ↥s) (fun Q ω =>
    bankRootScaledSelectedRemainder M Q.1 m r ω) ω

noncomputable def bankRootInverseRemainderHistory (Q : TriadicCube 2)
    (M : ABKModel 2) (m : ℤ) (r : RootRow)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  bankHistoryPrefactor * ∑' j : ℕ,
    bankHistoryAlpha^j * bankFiniteRootRemainderMax (descendantsAtDepth Q j)
      M m r ω

noncomputable def bankFiniteRootHistoryMax (s : Finset (TriadicCube 2))
    (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  historyFiniteMax (Finset.univ : Finset ↥s) (fun Q ω =>
    bankRootInverseHistory Q.1 M m J weights ω) ω

noncomputable def bankFiniteRootRemainderHistoryMax (s : Finset (TriadicCube 2))
    (M : ABKModel 2) (m : ℤ) (r : RootRow)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  historyFiniteMax (Finset.univ : Finset ↥s) (fun Q ω =>
    bankRootInverseRemainderHistory Q.1 M m r ω) ω

noncomputable def bankRootInverseRemainderHistoryL256Bound
    (M : ABKModel 2) (Q : TriadicCube 2) (m : ℤ) (r : RootRow) : ℝ≥0∞ :=
  bankHistoryPrefactor * ∑' j : ℕ, bankHistoryAlpha^j *
    (((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) *
      (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) *
        (ENNReal.ofReal (rootLi M.gamma r * selectedRootTiny (rootH0 r)) +
          ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
            rootDensityErrorBudget M.gamma r))))

theorem bank_root_selected_remainder_measurable (M : ABKModel 2)
    (Q : TriadicCube 2) (m J : ℤ) (weights : ℤ → ℝ) (r : RootRow)
    (hPointwise : PointwiseRootConclusion M Q m J weights r)
    (hSelected : FixedSelectedHeightConclusion M Q r) :
    Measurable (bankRootSelectedRemainder M Q r) := by
  rcases hPointwise with ⟨hEmeas, _, _⟩
  rcases hSelected with ⟨hHmeas, _, _, _, _⟩
  have hH : Measurable (rootSelectedHeight M Q r) := by
    simpa only [rootSelectedHeight] using hHmeas
  have hClock : Measurable
      (selectedHeightClock M.gamma (rootSelectedHeight M Q r)) := by
    exact (measurable_of_countable (fun k : ℕ =>
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((k:ℝ)-38))))).comp hH
  have hTail : Measurable
      (selectedRootClockTail M.gamma (rootH0 r) (rootSelectedHeight M Q r)) := by
    rw [show selectedRootClockTail M.gamma (rootH0 r) (rootSelectedHeight M Q r) =
      fun ω => if rootH0 r + 11 < rootSelectedHeight M Q r ω
        then selectedHeightClock M.gamma (rootSelectedHeight M Q r) ω else 0 by
      funext ω
      exact selected_root_clock_tail_eq M.gamma (rootH0 r)
        (rootSelectedHeight M Q r) ω]
    exact Measurable.ite (measurableSet_lt measurable_const hH) hClock measurable_const
  exact (hTail.const_mul _).add hEmeas

theorem bank_root_inverse_response_le_baseline_add_remainder
    (M : ABKModel 2) (Q : TriadicCube 2) (m J : ℤ) (weights : ℤ → ℝ)
    (r : RootRow) (hPointwise : PointwiseRootConclusion M Q m J weights r) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ENNReal.ofReal (rootInverseResponse M Q m J weights ω) ≤
        bankRootResponseBaseline M Q m r + bankRootScaledSelectedRemainder M Q m r ω := by
  let C := bankRootFrameFactor M Q m
  let L := ENNReal.ofReal (rootLi M.gamma r)
  let B := ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27)))
  let E := positiveRootError M Q r
  have hresponse := hPointwise.2.1
  filter_upwards [hresponse] with ω hω
  have hclock := bank_selected_clock_le_base_add_tail M Q r ω
  have hinner : L * selectedHeightClock M.gamma (rootSelectedHeight M Q r) ω + E ω ≤
      L * (B + selectedRootClockTail M.gamma (rootH0 r)
        (rootSelectedHeight M Q r) ω) + E ω := by
    exact add_le_add (mul_le_mul_of_nonneg_left hclock bot_le) le_rfl
  have hsource : ENNReal.ofReal (rootInverseResponse M Q m J weights ω) ≤
      C * (L * (B + selectedRootClockTail M.gamma (rootH0 r)
        (rootSelectedHeight M Q r) ω) + E ω) := by
    apply le_trans ?_ (mul_le_mul_of_nonneg_left hinner bot_le)
    simpa [C, L, E, bankRootFrameFactor, rootSelectedHeight] using hω
  calc
    _ ≤ C * (L * (B + selectedRootClockTail M.gamma (rootH0 r)
        (rootSelectedHeight M Q r) ω) + E ω) := hsource
    _ = bankRootResponseBaseline M Q m r + bankRootScaledSelectedRemainder M Q m r ω := by
      simp [bankRootResponseBaseline, bankRootScaledSelectedRemainder,
        bankRootSelectedRemainder, bankRootFrameFactor, C, L, B, E,
        mul_add, mul_assoc, add_comm, add_left_comm]

theorem bank_L256_formula {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    eLpNorm f 256 μ = (∫⁻ ω, (f ω)^256 ∂μ)^(1/256 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  norm_num [enorm_eq_self]

theorem bank_constant_mul_L256 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (c : ℝ≥0∞) (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    eLpNorm (fun ω => c*f ω) 256 μ = c*eLpNorm f 256 μ := by
  rw [bank_L256_formula μ _ (hf.const_mul c)]
  simp only [mul_pow]
  rw [lintegral_const_mul (c^256) (hf.pow_const 256), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have hc : (c^256)^(1/256:ℝ) = c := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [hc, ← bank_L256_formula μ f hf]

theorem bank_root_selected_remainder_L256 (M : ABKModel 2)
    (Q : TriadicCube 2) (m J : ℤ) (weights : ℤ → ℝ) (r : RootRow)
    (hPointwise : PointwiseRootConclusion M Q m J weights r)
    (hSelected : FixedSelectedHeightConclusion M Q r) :
    eLpNorm (bankRootSelectedRemainder M Q r) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (rootLi M.gamma r * selectedRootTiny (rootH0 r)) +
        ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
          rootDensityErrorBudget M.gamma r) := by
  rcases hPointwise with ⟨_, _, hError⟩
  rcases hSelected with ⟨hHmeas, _, _, _, hClockBounds⟩
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let L := ENNReal.ofReal (rootLi M.gamma r)
  let T := selectedRootClockTail M.gamma (rootH0 r) (rootSelectedHeight M Q r)
  let E := positiveRootError M Q r
  have hLpos : 0 ≤ rootLi M.gamma r := bank_root_Li_nonneg M.gamma r
  have hTmeas : Measurable T := by
    have hH : Measurable (rootSelectedHeight M Q r) := by
      simpa only [rootSelectedHeight] using hHmeas
    have hClock : Measurable (selectedHeightClock M.gamma (rootSelectedHeight M Q r)) :=
      (measurable_of_countable (fun k : ℕ =>
        ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((k:ℝ)-38))))).comp hH
    rw [show T = fun ω => if rootH0 r + 11 < rootSelectedHeight M Q r ω
      then selectedHeightClock M.gamma (rootSelectedHeight M Q r) ω else 0 by
      funext ω
      exact selected_root_clock_tail_eq M.gamma (rootH0 r)
        (rootSelectedHeight M Q r) ω]
    exact Measurable.ite (measurableSet_lt measurable_const hH) hClock measurable_const
  have hTail := hClockBounds 256 (by norm_num) (by norm_num)
  have hTail' : eLpNorm T 256 μ ≤ ENNReal.ofReal (selectedRootTiny (rootH0 r)) := by
    simpa only [T, μ, ENNReal.ofReal_ofNat] using hTail.2.1
  have hError' : eLpNorm E 256 μ ≤
      ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
        rootDensityErrorBudget M.gamma r) := by
    simpa only [E, μ, ENNReal.ofReal_ofNat] using
      (hError 256 (by norm_num) (by norm_num)).1
  have hscale : eLpNorm (fun ω => L*T ω) 256 μ = L*eLpNorm T 256 μ :=
    bank_constant_mul_L256 μ L T hTmeas
  have hsum : eLpNorm (fun ω => L*T ω + E ω) 256 μ ≤
      L*ENNReal.ofReal (selectedRootTiny (rootH0 r)) +
        ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
          rootDensityErrorBudget M.gamma r) := by
    calc
      _ ≤ eLpNorm (fun ω => L*T ω) 256 μ + eLpNorm E 256 μ :=
        eLpNorm_add_le (by norm_num)
      _ ≤ L*ENNReal.ofReal (selectedRootTiny (rootH0 r)) +
          ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
            rootDensityErrorBudget M.gamma r) := by
        rw [hscale]
        exact add_le_add (mul_le_mul_of_nonneg_left hTail' bot_le) hError'
  change eLpNorm (fun ω => L*T ω + E ω) 256 μ ≤ _
  simpa only [L, ENNReal.ofReal_mul hLpos] using hsum

theorem bank_root_scaled_selected_remainder_L256 (M : ABKModel 2)
    (Q : TriadicCube 2) (m J : ℤ) (weights : ℤ → ℝ) (r : RootRow)
    (hPointwise : PointwiseRootConclusion M Q m J weights r)
    (hSelected : FixedSelectedHeightConclusion M Q r) :
    eLpNorm (bankRootScaledSelectedRemainder M Q m r)
        256 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      bankRootFrameFactor M Q m * (ENNReal.ofReal (rootLi M.gamma r *
        selectedRootTiny (rootH0 r)) +
        ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
          rootDensityErrorBudget M.gamma r)) := by
  change eLpNorm (fun ω => bankRootFrameFactor M Q m *
    bankRootSelectedRemainder M Q r ω) 256 (Cutoff.cutoffSampleLaw M).toMeasure ≤ _
  rw [bank_constant_mul_L256 _ _ _
    (bank_root_selected_remainder_measurable M Q m J weights r hPointwise hSelected)]
  exact mul_le_mul_of_nonneg_left
    (bank_root_selected_remainder_L256 M Q m J weights r hPointwise hSelected) bot_le

theorem bank_finite_root_response_split
    (M : ABKModel 2) (s : Finset (TriadicCube 2)) (ell m J : ℤ)
    (weights : ℤ → ℝ) (r : RootRow)
    (hscale : ∀ Q ∈ s, Q.scale = ell)
    (hPointwise : ∀ Q ∈ s, PointwiseRootConclusion M Q m J weights r) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      bankFiniteRootResponseMax s M m J weights ω ≤
        ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-ell+1:ℤ):ℝ)|)) *
          (ENNReal.ofReal (rootLi M.gamma r) *
            ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27)))) +
          bankFiniteRootRemainderMax s M m r ω := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let A := ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-ell+1:ℤ):ℝ)|)) *
    (ENNReal.ofReal (rootLi M.gamma r) *
      ENNReal.ofReal ((3:ℝ)^(2*M.gamma*((rootH0 r:ℝ)-27))))
  have hroot : ∀ Q : ↥s, ∀ᵐ ω ∂μ,
      ENNReal.ofReal (rootInverseResponse M Q.1 m J weights ω) ≤
        A + bankRootScaledSelectedRemainder M Q.1 m r ω := by
    intro Q
    have h := bank_root_inverse_response_le_baseline_add_remainder M Q.1 m J weights r
      (hPointwise Q.1 Q.2)
    filter_upwards [h] with ω hω
    have hscale' := hscale Q.1 Q.2
    simpa [A, bankRootResponseBaseline, bankRootFrameFactor, hscale'] using hω
  filter_upwards [ae_all_iff.mpr hroot] with ω hω
  change (Finset.univ : Finset ↥s).sup (fun Q =>
      ENNReal.ofReal (rootInverseResponse M Q.1 m J weights ω)) ≤
    A + (Finset.univ : Finset ↥s).sup (fun Q =>
      bankRootScaledSelectedRemainder M Q.1 m r ω)
  apply Finset.sup_le
  intro Q hQ
  calc
    ENNReal.ofReal (rootInverseResponse M Q.1 m J weights ω) ≤
        A + bankRootScaledSelectedRemainder M Q.1 m r ω := hω Q
    _ ≤ A + (Finset.univ : Finset ↥s).sup
        (fun Q => bankRootScaledSelectedRemainder M Q.1 m r ω) := by
      exact add_le_add le_rfl (Finset.le_sup
        (f := fun Q : ↥s => bankRootScaledSelectedRemainder M Q.1 m r ω) hQ)

theorem bank_root_inverse_history_split_of_pointwise
    (M : ABKModel 2) (h : ℝ) (Q : TriadicCube 2) (m J : ℤ)
    (hQ : Q.scale ≤ m) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hweights : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (r : RootRow) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m r)
    (hPointwiseRoot : ∀ (Q' : TriadicCube 2) (m' J' : ℤ)
      (_hQ' : Q'.scale ≤ m') (_hmJ' : m' ≤ J') (weights' : ℤ → ℝ)
      (_hweights' : ∀ k ∈ Finset.Ioc m' J', 0 ≤ weights' k ∧ weights' k ≤ 1)
      (r' : RootRow) (_hpast' : ∀ n < m', nativeInductionState M h n)
      (_hmean' : ClippedInverseMeanInput M m' r'),
      PointwiseRootConclusion M Q' m' J' weights' r') :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      bankRootInverseHistory Q M m J weights ω ≤
        bankRootInverseBaselineHistory Q M m r +
          bankRootInverseRemainderHistory Q M m r ω := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hPointwise : ∀ j : ℕ, ∀ V ∈ descendantsAtDepth Q j,
      PointwiseRootConclusion M V m J weights r := by
    intro j V hV
    have hVscale : V.scale ≤ m := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth hV]
      omega
    exact hPointwiseRoot V m J hVscale hmJ weights hweights r hpast hmean
  have hdepth : ∀ j : ℕ, ∀ᵐ ω ∂μ,
      bankFiniteRootResponseMax (descendantsAtDepth Q j) M m J weights ω ≤
        bankRootDepthBaseline M Q m r j +
          bankFiniteRootRemainderMax (descendantsAtDepth Q j) M m r ω := by
    intro j
    have hscale : ∀ V ∈ descendantsAtDepth Q j,
        V.scale = Q.scale-(j:ℤ) := by
      intro V hV
      exact scale_eq_sub_of_mem_descendantsAtDepth hV
    have h := bank_finite_root_response_split M (descendantsAtDepth Q j)
      (Q.scale-(j:ℤ)) m J weights r hscale (hPointwise j)
    simpa [bankRootDepthBaseline] using h
  filter_upwards [ae_all_iff.mpr hdepth] with ω hω
  have hsum : (∑' j : ℕ, bankHistoryAlpha^j *
        bankFiniteRootResponseMax (descendantsAtDepth Q j) M m J weights ω) ≤
      ∑' j : ℕ, bankHistoryAlpha^j *
        (bankRootDepthBaseline M Q m r j +
          bankFiniteRootRemainderMax (descendantsAtDepth Q j) M m r ω) := by
    exact ENNReal.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hω j)
      (show (0:ℝ≥0∞) ≤ bankHistoryAlpha^j from bot_le))
  have hsplit : (∑' j : ℕ, bankHistoryAlpha^j *
      (bankRootDepthBaseline M Q m r j +
        bankFiniteRootRemainderMax (descendantsAtDepth Q j) M m r ω)) =
      (∑' j : ℕ, bankHistoryAlpha^j * bankRootDepthBaseline M Q m r j) +
        ∑' j : ℕ, bankHistoryAlpha^j *
          bankFiniteRootRemainderMax (descendantsAtDepth Q j) M m r ω := by
    rw [show (fun j : ℕ => bankHistoryAlpha^j *
      (bankRootDepthBaseline M Q m r j +
        bankFiniteRootRemainderMax (descendantsAtDepth Q j) M m r ω)) =
      (fun j => bankHistoryAlpha^j * bankRootDepthBaseline M Q m r j +
        bankHistoryAlpha^j * bankFiniteRootRemainderMax (descendantsAtDepth Q j) M m r ω) by
        funext j
        rw [mul_add]]
    exact ENNReal.tsum_add
  calc
    _ ≤ bankHistoryPrefactor * ∑' j : ℕ, bankHistoryAlpha^j *
        (bankRootDepthBaseline M Q m r j +
          bankFiniteRootRemainderMax (descendantsAtDepth Q j) M m r ω) := by
      exact mul_le_mul_of_nonneg_left hsum bot_le
    _ = bankRootInverseBaselineHistory Q M m r +
        bankRootInverseRemainderHistory Q M m r ω := by
      rw [hsplit]
      simp [bankRootInverseBaselineHistory, bankRootInverseRemainderHistory, mul_add]

theorem bank_root_inverse_history_measurable (Q : TriadicCube 2)
    (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ) :
    Measurable (bankRootInverseHistory Q M m J weights) := by
  exact (Measurable.tsum (fun j =>
    (bank_depth_root_response_measurable Q j M m J weights).const_mul _)).const_mul _

theorem bank_L256_power {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (eLpNorm f 256 μ)^256 = ∫⁻ ω, (f ω)^256 ∂μ := by
  rw [bank_L256_formula μ f hf, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Convert an ENNReal history split into the real positive-split estimate.
The ENNReal remainder is first shown finite almost everywhere from its
order-256 norm, so `toReal` preserves the affine history bound. -/
theorem bank_ennreal_positive_split_L128_of_affine
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y R : Ω → ℝ≥0∞) (hY : Measurable Y) (hR : Measurable R)
    (A δ e : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) (he : 0 ≤ e)
    (hSplit : ∀ᵐ ω ∂μ, Y ω ≤ ENNReal.ofReal A + R ω)
    (hR256 : eLpNorm R 256 μ ≤ ENNReal.ofReal e) :
    eLpNorm (fun ω => (Y ω).toReal) 128 μ ≤
        ENNReal.ofReal A + ENNReal.ofReal e ∧
      eLpNorm (fun ω => positiveSplitRemainder (Y ω).toReal A δ) 128 μ ≤
        ENNReal.ofReal (1 / (4 * δ)) * ENNReal.ofReal e ^ 2 := by
  have hRpow : (eLpNorm R 256 μ) ^ 256 ≤ (ENNReal.ofReal e) ^ 256 :=
    pow_le_pow_left' hR256 256
  have hRint : (∫⁻ ω, (R ω) ^ 256 ∂μ) ≠ ∞ := by
    rw [← bank_L256_power μ R hR]
    exact ne_top_of_le_ne_top (by simp) hRpow
  have hRpowfinite : ∀ᵐ ω ∂μ, (R ω) ^ 256 < ∞ :=
    ae_lt_top (hR.pow_const 256) hRint
  have hRfinite : ∀ᵐ ω ∂μ, R ω < ∞ := hRpowfinite.mono fun ω hω => by
    by_contra htop
    have htop' : R ω = ∞ := by simpa using htop
    rw [htop'] at hω
    simp at hω
  have hYfinite : ∀ᵐ ω ∂μ, Y ω < ∞ := by
    filter_upwards [hSplit, hRfinite] with ω hω hRω
    exact lt_of_le_of_lt hω (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hRω⟩)
  let y : Ω → ℝ := fun ω => (Y ω).toReal
  let r : Ω → ℝ := fun ω => (R ω).toReal
  have hy : Measurable y := ENNReal.measurable_toReal.comp hY
  have hr : Measurable r := ENNReal.measurable_toReal.comp hR
  have hAffine : ∀ᵐ ω ∂μ, y ω ≤ A + r ω := by
    filter_upwards [hSplit, hRfinite, hYfinite] with ω hω hRω hYω
    have hsum : ENNReal.ofReal A + R ω < ∞ :=
      ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hRω⟩
    have hω' := ENNReal.toReal_mono hsum.ne hω
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hRω.ne,
      ENNReal.toReal_ofReal hA] at hω'
    exact hω'
  have hRnorm : eLpNorm r 256 μ ≤ ENNReal.ofReal e := by
    calc
      _ = eLpNorm (ENNReal.ofReal ∘ r) 256 μ := by
        symm
        exact eLpNorm_ofReal r (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
      _ = eLpNorm R 256 μ := eLpNorm_congr_ae (ofReal_toReal_ae_eq hRfinite)
      _ ≤ _ := hR256
  have hExcess : eLpNorm (fun ω => max 0 (y ω - A)) 256 μ ≤ ENNReal.ofReal e := by
    have hmono := eLpNorm_mono_ae_real (p := (256 : ℝ≥0∞))
      ((measurable_const.max (hy.sub_const A)).aestronglyMeasurable)
      (by
        filter_upwards [hAffine] with ω hAff
        have hrω : 0 ≤ r ω := ENNReal.toReal_nonneg
        have hyA : y ω - A ≤ r ω := by linarith only [hAff]
        calc
          ‖max (0 : ℝ) (y ω - A)‖ = max 0 (y ω - A) := by
            rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left (0 : ℝ) _)]
          _ ≤ r ω := max_le hrω hyA)
    exact hmono.trans hRnorm
  have htotal := bank_L128_cap_of_L256_excess μ y hy
    (fun _ => ENNReal.toReal_nonneg) A e hA he hExcess
  have hpositive := positive_split_L128_of_cap μ y hy A δ hδ
    (ENNReal.ofReal e) hExcess
  exact ⟨by simpa only [y] using htotal, by simpa only [y] using hpositive⟩

theorem bank_ennreal_tsum_L256 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ℕ → Ω → ℝ≥0∞) (hf : ∀ j, Measurable (f j)) :
    eLpNorm (fun ω => ∑' j, f j ω) 256 μ ≤ ∑' j, eLpNorm (f j) 256 μ := by
  let partialSum (N : ℕ) (ω : Ω) : ℝ≥0∞ := ∑ j ∈ Finset.range N, f j ω
  let S : ℝ≥0∞ := ∑' j, eLpNorm (f j) 256 μ
  by_cases hS : S = ⊤
  · simp [S, hS]
  have hpart (N : ℕ) : Measurable (partialSum N) :=
    Finset.measurable_sum _ (fun j _ => hf j)
  have hbound (N : ℕ) : eLpNorm (partialSum N) 256 μ ≤ S := by
    have he : (∑ j ∈ Finset.range N, f j) = partialSum N := by
      funext ω
      simp only [partialSum, Finset.sum_apply]
    have hb := eLpNorm_sum_le (μ := μ) (f := f) (s := Finset.range N)
      (by norm_num : (1:ℝ≥0∞) ≤ 256)
    rw [he] at hb
    exact hb.trans (ENNReal.sum_le_tsum (Finset.range N))
  have hpow (N : ℕ) : (∫⁻ ω, (partialSum N ω)^256 ∂μ) ≤ S^256 := by
    rw [← bank_L256_power μ (partialSum N) (hpart N)]
    exact pow_le_pow_left' (hbound N) 256
  have hmono : Monotone (fun N ω => (partialSum N ω)^256) := by
    intro N K hNK ω
    apply pow_le_pow_left' _ 256
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hNK)
  have hmoment :
      (eLpNorm (fun ω => ∑' j, f j ω) 256 μ)^256 ≤ S^256 := by
    rw [bank_L256_power μ _ (Measurable.tsum hf)]
    calc
      _ = ∫⁻ ω, ⨆ N, (partialSum N ω)^256 ∂μ := by
        apply lintegral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          dsimp only
          rw [ENNReal.tsum_eq_iSup_nat, ENNReal.iSup_pow])
      _ = ⨆ N, ∫⁻ ω, (partialSum N ω)^256 ∂μ :=
        lintegral_iSup (fun N => (hpart N).pow_const 256) hmono
      _ ≤ S^256 := iSup_le hpow
  have hroot : eLpNorm (fun ω => ∑' j, f j ω) 256 μ ≤ S := by
    apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < 256)).mp
    simpa only [show (256:ℝ)=((256:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast] using hmoment
  simpa only [S] using hroot

/-- The exact finite maximum payment at order 256. -/
theorem bank_finite_max_L256 {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (f : ι → Ω → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (B : ℝ≥0∞)
    (hB : ∀ i ∈ s, eLpNorm (f i) 256 μ ≤ B) :
    eLpNorm (historyFiniteMax s f) 256 μ ≤ (s.card : ℝ≥0∞)^(1/256 : ℝ)*B := by
  have hpow (x : ι → ℝ≥0∞) :
      (s.sup x)^256 ≤ ∑ i ∈ s, (x i)^256 := by
    rw [Finset.apply_sup_eq_sup_comp_of_linearOrder (fun y : ℝ≥0∞ => y^256)
      (fun _ _ h => pow_le_pow_left' h 256) (by norm_num)]
    apply Finset.sup_le
    intro i hi
    exact Finset.single_le_sum (fun j _ => (zero_le : (0:ℝ≥0∞) ≤ (x j)^256)) hi
  have hmoment : (∫⁻ ω, (historyFiniteMax s f ω)^256 ∂μ) ≤
      (s.card : ℝ≥0∞)*B^256 := by
    calc
      _ ≤ ∫⁻ ω, ∑ i ∈ s, (f i ω)^256 ∂μ :=
        lintegral_mono (fun ω => by simpa only [historyFiniteMax] using hpow (fun i => f i ω))
      _ = ∑ i ∈ s, ∫⁻ ω, (f i ω)^256 ∂μ :=
        lintegral_finsetSum _ (fun i _ => (hf i).pow_const 256)
      _ ≤ ∑ _i ∈ s, B^256 := Finset.sum_le_sum (fun i hi => by
        rw [← bank_L256_power μ (f i) (hf i)]
        exact pow_le_pow_left' (hB i hi) 256)
      _ = (s.card : ℝ≥0∞)*B^256 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  rw [bank_L256_formula μ _ (history_finite_max_measurable s f hf)]
  have h := ENNReal.rpow_le_rpow hmoment (by norm_num : (0:ℝ) ≤ 1/256)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h
  have hBpow : (B^256)^(1/256 : ℝ) = B := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rwa [hBpow] at h

theorem bank_finite_root_remainder_L256
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (s : Finset (TriadicCube 2))
    (ell m J : ℤ) (weights : ℤ → ℝ) (r : RootRow)
    (hscale : ∀ Q ∈ s, Q.scale = ell)
    (hpast : ∀ Q ∈ s, ∀ k ≤ Q.scale-(rootH0 r:ℤ)+40,
      nativeInductionState M h k)
    (hPointwise : ∀ Q ∈ s, PointwiseRootConclusion M Q m J weights r) :
    eLpNorm (bankFiniteRootRemainderMax s M m r) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      (s.card:ℝ≥0∞)^(1/256:ℝ) *
        (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-ell+1:ℤ):ℝ)|)) *
          (ENNReal.ofReal (rootLi M.gamma r * selectedRootTiny (rootH0 r)) +
            ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
              rootDensityErrorBudget M.gamma r))) := by
  classical
  let f : ↥s → Cutoff.CutoffSample 2 → ℝ≥0∞ := fun Q ω =>
    bankRootScaledSelectedRemainder M Q.1 m r ω
  let C := ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-ell+1:ℤ):ℝ)|))
  let B := C * (ENNReal.ofReal (rootLi M.gamma r *
    selectedRootTiny (rootH0 r)) +
      ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
        rootDensityErrorBudget M.gamma r))
  have hf : ∀ Q : ↥s, Measurable (f Q) := by
    intro Q
    exact (bank_root_selected_remainder_measurable M Q.1 m J weights r
      (hPointwise Q.1 Q.2) (q3_fixed_selected_height M h hM hg Q.1 r
        (hpast Q.1 Q.2))).const_mul _
  have hB : ∀ Q ∈ (Finset.univ : Finset ↥s), eLpNorm (f Q) 256
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ B := by
    intro Q _
    have hselected : FixedSelectedHeightConclusion M Q.1 r :=
      q3_fixed_selected_height M h hM hg Q.1 r (hpast Q.1 Q.2)
    have hrem := bank_root_scaled_selected_remainder_L256 M Q.1 m J weights r
      (hPointwise Q.1 Q.2) hselected
    have hscale' := hscale Q.1 Q.2
    simpa [f, B, C, bankRootFrameFactor, hscale'] using hrem
  have hpop := bank_finite_max_L256 (Cutoff.cutoffSampleLaw M).toMeasure
    (Finset.univ : Finset ↥s) f hf B hB
  have hcard : (Finset.univ : Finset ↥s).card = s.card := by simp
  change eLpNorm (historyFiniteMax (Finset.univ : Finset ↥s) f) 256
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ _
  simpa [bankFiniteRootRemainderMax, f, B, C, hcard] using hpop

theorem bank_root_inverse_remainder_history_L256_of_pointwise
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m J : ℤ)
    (hQ : Q.scale ≤ m) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hweights : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (r : RootRow) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m r)
    (hPointwiseRoot : ∀ (Q' : TriadicCube 2) (m' J' : ℤ)
      (_hQ' : Q'.scale ≤ m') (_hmJ' : m' ≤ J') (weights' : ℤ → ℝ)
      (_hweights' : ∀ k ∈ Finset.Ioc m' J', 0 ≤ weights' k ∧ weights' k ≤ 1)
      (r' : RootRow) (_hpast' : ∀ n < m', nativeInductionState M h n)
      (_hmean' : ClippedInverseMeanInput M m' r'),
      PointwiseRootConclusion M Q' m' J' weights' r') :
    eLpNorm (bankRootInverseRemainderHistory Q M m r) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤
      bankHistoryPrefactor * ∑' j : ℕ, bankHistoryAlpha^j *
        (((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) *
          (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) *
            (ENNReal.ofReal (rootLi M.gamma r * selectedRootTiny (rootH0 r)) +
              ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
                rootDensityErrorBudget M.gamma r)))) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let F (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
    bankHistoryAlpha^j * bankFiniteRootRemainderMax (descendantsAtDepth Q j)
      M m r ω
  have hH0 : 333 ≤ rootH0 r := by cases r <;> norm_num [rootH0]
  have hPointwise : ∀ j : ℕ, ∀ V ∈ descendantsAtDepth Q j,
      PointwiseRootConclusion M V m J weights r := by
    intro j V hV
    have hVscale : V.scale ≤ m := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth hV]
      omega
    exact hPointwiseRoot V m J hVscale hmJ weights hweights r hpast hmean
  have hpastV : ∀ j : ℕ, ∀ V ∈ descendantsAtDepth Q j,
      ∀ k ≤ V.scale-(rootH0 r:ℤ)+40, nativeInductionState M h k := by
    intro j V hV k hk
    have hVscale : V.scale ≤ m := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth hV]
      omega
    apply hpast
    omega
  have hF : ∀ j, Measurable (F j) := by
    intro j
    exact (history_finite_max_measurable (Finset.univ : Finset ↥(descendantsAtDepth Q j))
      (fun V ω => bankRootScaledSelectedRemainder M V.1 m r ω) (fun V => by
        exact (bank_root_selected_remainder_measurable M V.1 m J weights r
          (hPointwise j V.1 V.2)
          (q3_fixed_selected_height M h hM hg V.1 r (hpastV j V.1 V.2))).const_mul _)).const_mul _
  have hsum := bank_ennreal_tsum_L256 μ F hF
  have hterm (j : ℕ) : eLpNorm (F j) 256 μ ≤
      bankHistoryAlpha^j *
        (((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) *
          (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) *
            (ENNReal.ofReal (rootLi M.gamma r * selectedRootTiny (rootH0 r)) +
              ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
                rootDensityErrorBudget M.gamma r)))) := by
    rw [show F j = (fun ω => bankHistoryAlpha^j *
      bankFiniteRootRemainderMax (descendantsAtDepth Q j) M m r ω) by rfl]
    have hmeas : Measurable
        (bankFiniteRootRemainderMax (descendantsAtDepth Q j) M m r) := by
      exact history_finite_max_measurable _ _ (fun V => by
        exact (bank_root_selected_remainder_measurable M V.1 m J weights r
          (hPointwise j V.1 V.2)
          (q3_fixed_selected_height M h hM hg V.1 r (hpastV j V.1 V.2))).const_mul _)
    rw [bank_constant_mul_L256 μ _ _ hmeas]
    have hscale : ∀ V ∈ descendantsAtDepth Q j, V.scale = Q.scale-(j:ℤ) := by
      intro V hV
      exact scale_eq_sub_of_mem_descendantsAtDepth hV
    have hpast' : ∀ V ∈ descendantsAtDepth Q j,
        ∀ k ≤ V.scale-(rootH0 r:ℤ)+40, nativeInductionState M h k :=
      hpastV j
    have hdepth := bank_finite_root_remainder_L256 M h hM hg
      (descendantsAtDepth Q j) (Q.scale-(j:ℤ)) m J weights r hscale hpast'
      (hPointwise j)
    have hdepth' : eLpNorm
        (bankFiniteRootRemainderMax (descendantsAtDepth Q j) M m r) 256 μ ≤
        ((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) *
          (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) *
            (ENNReal.ofReal (rootLi M.gamma r * selectedRootTiny (rootH0 r)) +
              ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
                rootDensityErrorBudget M.gamma r))) := by
      simpa only [μ, ENNReal.ofReal_ofNat] using hdepth
    exact mul_le_mul_of_nonneg_left hdepth'
      (show (0:ℝ≥0∞) ≤ bankHistoryAlpha^j from bot_le)
  have hsum' : (∑' j : ℕ, eLpNorm (F j) 256 μ) ≤
      ∑' j : ℕ, bankHistoryAlpha^j *
        (((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) *
          (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) *
            (ENNReal.ofReal (rootLi M.gamma r * selectedRootTiny (rootH0 r)) +
              ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
                rootDensityErrorBudget M.gamma r)))) :=
    ENNReal.tsum_le_tsum hterm
  have hpref : 0 ≤ bankHistoryPrefactor := bot_le
  change eLpNorm (fun ω => bankHistoryPrefactor * ∑' j,
      bankHistoryAlpha^j * bankFiniteRootRemainderMax (descendantsAtDepth Q j)
        M m r ω) 256 μ ≤ _
  rw [bank_constant_mul_L256 μ bankHistoryPrefactor _ (Measurable.tsum hF)]
  calc
    _ ≤ bankHistoryPrefactor * ∑' j, eLpNorm (F j) 256 μ :=
      mul_le_mul_of_nonneg_left hsum hpref
    _ ≤ bankHistoryPrefactor * ∑' j : ℕ, bankHistoryAlpha^j *
        (((descendantsAtDepth Q j).card:ℝ≥0∞)^(1/256:ℝ) *
          (ENNReal.ofReal ((3:ℝ)^(2*M.gamma*|((m-(Q.scale-(j:ℤ))+1:ℤ):ℝ)|)) *
            (ENNReal.ofReal (rootLi M.gamma r * selectedRootTiny (rootH0 r)) +
              ENNReal.ofReal (rootMatrixErrorBudget M.gamma 256 r +
                rootDensityErrorBudget M.gamma r)))) :=
      mul_le_mul_of_nonneg_left hsum' hpref

theorem bank_root_inverse_remainder_history_measurable
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (m J : ℤ)
    (hQ : Q.scale ≤ m) (hmJ : m ≤ J) (weights : ℤ → ℝ)
    (hweights : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (r : RootRow) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m r)
    (hPointwiseRoot : ∀ (Q' : TriadicCube 2) (m' J' : ℤ)
      (_hQ' : Q'.scale ≤ m') (_hmJ' : m' ≤ J') (weights' : ℤ → ℝ)
      (_hweights' : ∀ k ∈ Finset.Ioc m' J', 0 ≤ weights' k ∧ weights' k ≤ 1)
      (r' : RootRow) (_hpast' : ∀ n < m', nativeInductionState M h n)
      (_hmean' : ClippedInverseMeanInput M m' r'),
      PointwiseRootConclusion M Q' m' J' weights' r') :
    Measurable (bankRootInverseRemainderHistory Q M m r) := by
  have hH0 : 333 ≤ rootH0 r := by cases r <;> norm_num [rootH0]
  have hpastV : ∀ j : ℕ, ∀ V ∈ descendantsAtDepth Q j,
      ∀ k ≤ V.scale-(rootH0 r:ℤ)+40, nativeInductionState M h k := by
    intro j V hV k hk
    apply hpast
    have hVscale := scale_eq_sub_of_mem_descendantsAtDepth hV
    omega
  have hPointwise : ∀ j : ℕ, ∀ V ∈ descendantsAtDepth Q j,
      PointwiseRootConclusion M V m J weights r := by
    intro j V hV
    have hVscale : V.scale ≤ m := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth hV]
      omega
    exact hPointwiseRoot V m J hVscale hmJ weights hweights r hpast hmean
  have hF : ∀ j : ℕ,
      Measurable (bankFiniteRootRemainderMax (descendantsAtDepth Q j) M m r) := by
    intro j
    exact history_finite_max_measurable _ _ (fun V => by
      have hVscale : V.1.scale ≤ m := by
        rw [scale_eq_sub_of_mem_descendantsAtDepth V.2]
        omega
      exact (bank_root_selected_remainder_measurable M V.1 m J weights r
        (hPointwise j V.1 V.2)
        (q3_fixed_selected_height M h hM hg V.1 r (hpastV j V.1 V.2))).const_mul _)
  exact (Measurable.tsum (fun j => (hF j).const_mul _)).const_mul _

end ASDExplicitGamma.Inverse
end
