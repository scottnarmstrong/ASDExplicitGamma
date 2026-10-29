module

public import ASDExplicitGamma.Inverse.BankLocalRootGeometry
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.BankOnePassHeat
public import ASDExplicitGamma.Inverse.BankOnePassMoments
public import ASDExplicitGamma.Inverse.ClippedMatrixEntryCap

/-! The actual local histories and their cubic moment during a forty-shell insertion. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

noncomputable def bankOnePassLocalHistory (M : ABKModel 2) (k : ℤ) (s : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 k) 5) M k (k+40)
    (bankPartialInsertionWeights k s t) ω).toReal

theorem bank_one_pass_local_geometry (k : ℤ) :
    (∀ Q ∈ bankLocalRoots (originCube 2 k) 5, Q.scale ≤ k ∧ k-Q.scale ≤ 5) ∧
      (bankLocalRoots (originCube 2 k) 5).card ≤ 6*9^45 :=
  bank_local_roots_geometry (originCube 2 k) 5 le_rfl

theorem bank_one_pass_local_measurable (M : ABKModel 2) (k : ℤ) (s : ℕ) (t : ℝ) :
    Measurable (bankOnePassLocalHistory M k s t) :=
  ENNReal.measurable_toReal.comp (history_finite_max_measurable _ _
    (fun Q => bank_root_inverse_history_measurable Q.1 M k (k+40)
      (bankPartialInsertionWeights k s t)))

theorem bank_one_pass_partial_coefficient (M : ABKModel 2) (k : ℤ)
    (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    attenuatedCoefficient M k (k+40) (bankPartialInsertionWeights k s t) ω =
      (Model.partialInsertedCoefficient M (k+(s:ℤ)-1) t ω).toFun := by
  funext x
  rw [bank_partial_insertion_coefficient M k s hs]
  have he : k+(s:ℤ)-1+1=k+(s:ℤ) := by omega
  change _ = Cutoff.coefficientCutoff M.nu (k+(s:ℤ)-1) ω x+
    Real.sqrt t • (ω.1 (k+(s:ℤ)-1+1)).forgetShell x
  rw [he]

theorem bank_one_pass_local_L128 (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (k : ℤ) (s : ℕ) (t : ℝ) (ht : t ≤ 1)
    (hpast : ∀ n < k, nativeInductionState M h n) :
    eLpNorm (bankOnePassLocalHistory M k s t) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (159/100:ℝ) := by
  have hgeometry := bank_one_pass_local_geometry k
  have hh := first_local_inverse_bank M h hM hg (bankLocalRoots (originCube 2 k) 5) k (k+40)
    (by omega) (bankPartialInsertionWeights k s t)
    (fun i _ => bank_partial_insertion_weights_bounds k s t ht i)
    hgeometry.1 hgeometry.2 hpast
  have he := eLpNorm_congr_ae (p:=128) (ofReal_toReal_ae_eq hh.history_finite)
  have he' : eLpNorm (bankOnePassLocalHistory M k s t) 128 (Cutoff.cutoffSampleLaw M).toMeasure =
      eLpNorm (bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 k) 5) M k (k+40)
        (bankPartialInsertionWeights k s t)) 128 (Cutoff.cutoffSampleLaw M).toMeasure := by
    calc
      _ = eLpNorm (fun ω => ENNReal.ofReal (bankOnePassLocalHistory M k s t ω)) 128
          (Cutoff.cutoffSampleLaw M).toMeasure :=
        (eLpNorm_ofReal _ (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)).symm
      _ = _ := he
  exact he'.trans_le (by simpa only [inverseBankCap,Rat.cast_div,Rat.cast_ofNat] using hh.total_L128)

theorem bank_one_pass_local_cubic (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (k : ℤ) (s : ℕ) (t : ℝ) (ht : t ≤ 1)
    (hpast : ∀ n < k, nativeInductionState M h n) :
    Integrable (fun ω => (bankOnePassLocalHistory M k s t ω)^3) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, (bankOnePassLocalHistory M k s t ω)^3 ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        (159/100:ℝ)^3 :=
  bank_cubic_integral_of_L128 _ _ (bank_one_pass_local_measurable M k s t)
    (fun _ => ENNReal.toReal_nonneg) _ (by norm_num)
    (bank_one_pass_local_L128 M h hM hg k s t ht hpast)


/-- The fixed-frame trace is bounded by twice the same actual local history
whose L128 cap was proved above. This comparison holds on the common finite-history event. -/
theorem bank_one_pass_trace_le_local_history
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (k : ℤ) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (hpast : ∀ n < k, nativeInductionState M h n) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      bankInverseTrace k (Model.partialInsertedCoefficient M (k+(s:ℤ)-1) t ω).toFun
        (Annealed.sigmaBar M k:ℝ) ≤ 2*bankOnePassLocalHistory M k s t ω := by
  have hgeometry := bank_one_pass_local_geometry k
  have hbank := first_local_inverse_bank M h hM hg (bankLocalRoots (originCube 2 k) 5) k (k+40)
    (by omega) (bankPartialInsertionWeights k s t)
    (fun i _ => bank_partial_insertion_weights_bounds k s t ht.2 i)
    hgeometry.1 hgeometry.2 hpast
  obtain ⟨ell,hK⟩ := Gaussian.exists_originCube_containing_compact _
    (isBounded_cubeSet (originCube 2 k)).isCompact_closure
  filter_upwards [hbank.history_finite] with ω hfinite
  have hcoeff := bank_one_pass_partial_coefficient M k s hs t ω
  have hEll := Model.partialInsertedCoefficient_isEllipticFieldOn M ell (k+(s:ℤ)-1) ω ht
    (measurableSet_openCubeSet (originCube 2 k))
    (fun _ hx => hK (subset_closure (openCubeSet_subset_cubeSet _ hx)))
  rw [← hcoeff] at hEll
  have hh := bank_root_response_le_history (originCube 2 k) M k (k+40)
    (bankPartialInsertionWeights k s t) ω hEll
  have hmax : bankRootInverseHistory (originCube 2 k) M k (k+40)
      (bankPartialInsertionWeights k s t) ω ≤
        bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 k) 5) M k (k+40)
          (bankPartialInsertionWeights k s t) ω := by
    have hm := bank_local_roots_self (originCube 2 k) 5
    have hh := bank_member_history_le M (bankLocalRoots (originCube 2 k) 5)
      (originCube 2 k) hm k (k+40)
      (bankPartialInsertionWeights k s t) ω
    exact hh
  have hnorm := ENNReal.toReal_mono hfinite.ne (hh.trans hmax)
  simp only [rootInverseResponse] at hnorm
  rw [ENNReal.toReal_ofReal (mul_nonneg (Annealed.sigmaBar_characterization M k).1.le
    (norm_nonneg _))] at hnorm
  have htrace : bankInverseTrace k (Model.partialInsertedCoefficient M (k+(s:ℤ)-1) t ω).toFun
      (Annealed.sigmaBar M k:ℝ) ≤
        2*rootInverseResponse M (originCube 2 k) k (k+40) (bankPartialInsertionWeights k s t) ω := by
    let A := (coarseBlockMatrix (cubeSet (originCube 2 k))
      (Model.partialInsertedCoefficient M (k+(s:ℤ)-1) t ω).toFun).lowerRight
    have h0 := (le_abs_self (A 0 0)).trans (clipped_matrix_entry_abs_le_norm A 0 0)
    have h1 := (le_abs_self (A 1 1)).trans (clipped_matrix_entry_abs_le_norm A 1 1)
    have hh := add_le_add (mul_le_mul_of_nonneg_left h0 (Annealed.sigmaBar_characterization M k).1.le)
      (mul_le_mul_of_nonneg_left h1 (Annealed.sigmaBar_characterization M k).1.le)
    simp only [bankInverseTrace,Fin.sum_univ_two,rootInverseResponse,hcoeff]
    change (Annealed.sigmaBar M k:ℝ)*A 0 0+(Annealed.sigmaBar M k:ℝ)*A 1 1 ≤ _
    linarith only [hh]
  exact htrace.trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))

end ASDExplicitGamma.Inverse
