module

public import ASDExplicitGamma.Main.AffineMatrixSymmetry
public import ASDExplicitGamma.Main.AffinePartialMoments
public import ASDExplicitGamma.Scalar.MolecularCompetitor
public import Algsuperdiff.Section3.Cutoff.CoefficientFamily
public import Algsuperdiff.Section3.Cutoff.LawCarrier
public import Algsuperdiff.Section3.Cutoff.P4Bounds
public import Homogenization.Book.Ch04.RestrictionLaw
public import Homogenization.Book.Ch04.Theorems.CoarseObservables

/-! Measurability carriers for the actual partially inserted coarse matrix. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Frozen.Assumptions
open Homogenization.Book
open Homogenization.Book.Ch04

noncomputable section

private noncomputable def mainInsertionCoeffOn
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : 0 ≤ t ∧ t ≤ 1) (Q : TriadicCube 2) : Ch02.CoeffOn (Ch02.cubeDomain Q) := by
  classical
  let ell : ℤ := cubeOriginCoverScale Q
  let B : ℝ :=
    ((2 : ℝ) * 2 * Model.partialInsertedEntryBound M ell m ω ^ 2 + M.nu ^ 2) / M.nu
  have hEll : IsEllipticFieldOn M.nu B (openCubeSet Q)
      (Model.partialInsertedCoefficient M m t ω) := by
    simpa [B] using Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
      (measurableSet_openCubeSet Q)
      (by simpa [ell] using openCubeSet_subset_originCover Q)
  have hEllAE : IsAEEllipticFieldOn M.nu B (openCubeSet Q)
      (Model.partialInsertedCoefficient M m t ω).toFun :=
    IsAEEllipticFieldOn.of_isEllipticFieldOn hEll
  have hnu : M.nu ≤ B := by
    apply (le_div_iff₀ M.nu_pos).2
    nlinarith [sq_nonneg (Model.partialInsertedEntryBound M ell m ω)]
  refine {
    toCoeffField := (Model.partialInsertedCoefficient M m t ω).toFun
    lam := M.nu
    Lam := B
    lam_pos := M.nu_pos
    lam_le_Lam := hnu
    aeStronglyMeasurable := ?_
    aeElliptic := ?_ }
  · intro i j
    have hmeas : Measurable (fun x : Vec 2 =>
        restrictCoeffField (openCubeSet Q)
          (Model.partialInsertedCoefficient M m t ω).toFun x i j) := by
      have hEq : (fun x : Vec 2 =>
          restrictCoeffField (openCubeSet Q)
            (Model.partialInsertedCoefficient M m t ω).toFun x i j) =
          fun x => if x ∈ openCubeSet Q then
            (Model.partialInsertedCoefficient M m t ω).toFun x i j else 0 := by
        funext x
        by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, hx]
      rw [hEq]
      exact ((Model.partialInsertedCoefficient M m t ω).entry_measurable i j).ite
        (measurableSet_openCubeSet Q) measurable_const
    simpa [Ch02.cubeDomain_coe] using hmeas.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet Q)]
      with x hx
    exact hEll.2 x hx

private noncomputable def mainInsertionTriadicCoeffFamily
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : 0 ≤ t ∧ t ≤ 1) : Ch02.TriadicCoeffFamily 2 where
  coeffOn := mainInsertionCoeffOn M m t ω ht
  restrictsTo_of_subset := by
    intro Q R hQR
    exact Filter.EventuallyEq.rfl

private theorem mainInsertionTriadicCoeffFamily_aeeq
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : 0 ≤ t ∧ t ≤ 1)
    (h : AELocallyUniformlyEllipticField (Model.partialInsertedCoefficient M m t ω)) :
    Ch02.TriadicCoeffFamily.AEEq
      (triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (Model.partialInsertedCoefficient M m t ω) h)
      (mainInsertionTriadicCoeffFamily M m t ω ht) := by
  intro Q
  change (Model.partialInsertedCoefficient M m t ω).toFun =ᵐ[
    volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec 2))]
      (Model.partialInsertedCoefficient M m t ω).toFun
  exact Filter.EventuallyEq.rfl

private theorem mainInsertion_partialCoefficient_aelocallyUniformlyElliptic
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : 0 ≤ t ∧ t ≤ 1) :
    AELocallyUniformlyEllipticField (Model.partialInsertedCoefficient M m t ω) := by
  intro Q
  let ell : ℤ := cubeOriginCoverScale Q
  have hEll : IsEllipticFieldOn M.nu
      (((2 : ℝ) * 2 * Model.partialInsertedEntryBound M ell m ω ^ 2 + M.nu ^ 2) / M.nu)
      (openCubeSet Q) (Model.partialInsertedCoefficient M m t ω).toFun := by
    exact Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
      (measurableSet_openCubeSet Q)
      (by simpa [ell] using openCubeSet_subset_originCover Q)
  have hEllA : IsAEEllipticFieldOn M.nu
      (((2 : ℝ) * 2 * Model.partialInsertedEntryBound M ell m ω ^ 2 + M.nu ^ 2) / M.nu)
      (openCubeSet Q) (Model.partialInsertedCoefficient M m t ω).toFun :=
    IsAEEllipticFieldOn.of_isEllipticFieldOn hEll
  have hnu : M.nu ≤
      ((2 * 2 * Model.partialInsertedEntryBound M ell m ω ^ 2 + M.nu ^ 2) / M.nu) := by
    apply (le_div_iff₀ M.nu_pos).2
    nlinarith [sq_nonneg (Model.partialInsertedEntryBound M ell m ω)]
  exact ⟨M.nu, _, M.nu_pos, hnu, hEllA⟩

private theorem mainInsertion_maxDescendantBMatrixNorm_le
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : 0 ≤ t ∧ t ≤ 1) (Q : TriadicCube 2) (n : ℕ) :
    maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ))
        (Model.partialInsertedCoefficient M m t ω) ≤
      8 * M.nu⁻¹ *
        (((2 : ℝ) * 2 * Model.partialInsertedEntryBound M (cubeOriginCoverScale Q) m ω ^ 2 +
          M.nu ^ 2) / M.nu) ^ 2 := by
  let a := Model.partialInsertedCoefficient M m t ω
  let F := mainInsertionTriadicCoeffFamily M m t ω ht
  let hlocal := mainInsertion_partialCoefficient_aelocallyUniformlyElliptic M m t ω ht
  let Fcanon := triadicCoeffFamilyOfAELocallyUniformlyEllipticField a hlocal
  have hAEEq : Ch02.TriadicCoeffFamily.AEEq Fcanon F :=
    mainInsertionTriadicCoeffFamily_aeeq M m t ω ht hlocal
  have hmaxEq (k : ℤ) :
      maxDescendantBMatrixNormCoeffFieldAtScale Q k a =
        Ch02.maxDescendantBMatrixNormAtScale Q k F := by
    unfold maxDescendantBMatrixNormCoeffFieldAtScale
    rw [dite_eq_left hlocal]
    exact Ch02.maxDescendantBMatrixNormAtScale_eq_ofAEEq hAEEq Q k
  let A : CoeffField 2 :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hEll : IsEllipticFieldOn M.nu
      (((2 : ℝ) * 2 * Model.partialInsertedEntryBound M (cubeOriginCoverScale Q) m ω ^ 2 +
        M.nu ^ 2) / M.nu) (openCubeSet Q) A := by
    simpa [A, F, mainInsertionTriadicCoeffFamily, mainInsertionCoeffOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using Ch02.pointwiseCoeffField_openCube_descendant_data Q (F.coeffOn Q)
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hmatrix :=
    Ch02.maxDescendantBMatrixNormAtScale_le_maxDescendantBBlockNormAtScale F Q hk
  have hblock :
      maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) A ≤
        8 * M.nu⁻¹ *
          (((2 : ℝ) * 2 * Model.partialInsertedEntryBound M (cubeOriginCoverScale Q) m ω ^ 2 +
            M.nu ^ 2) / M.nu) ^ 2 := by
    have hraw :=
      Homogenization.maxDescendantBBlockNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
        Q A hEll hData n
    have hdim : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
    rw [hdim] at hraw
    calc
      maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) A ≤
          4 * 2 * M.nu⁻¹ *
            (((2 : ℝ) * 2 * Model.partialInsertedEntryBound M (cubeOriginCoverScale Q) m ω ^ 2 +
              M.nu ^ 2) / M.nu) ^ 2 := hraw
      _ = 8 * M.nu⁻¹ *
            (((2 : ℝ) * 2 * Model.partialInsertedEntryBound M (cubeOriginCoverScale Q) m ω ^ 2 +
              M.nu ^ 2) / M.nu) ^ 2 := by ring
  rw [hmaxEq]
  exact hmatrix.trans hblock

private theorem mainInsertion_maxDescendantSigmaStarInvMatrixNorm_le
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : 0 ≤ t ∧ t ≤ 1) (Q : TriadicCube 2) (n : ℕ) :
    maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ))
        (Model.partialInsertedCoefficient M m t ω) ≤ 8 * M.nu⁻¹ := by
  let a := Model.partialInsertedCoefficient M m t ω
  let F := mainInsertionTriadicCoeffFamily M m t ω ht
  let hlocal := mainInsertion_partialCoefficient_aelocallyUniformlyElliptic M m t ω ht
  let Fcanon := triadicCoeffFamilyOfAELocallyUniformlyEllipticField a hlocal
  have hAEEq : Ch02.TriadicCoeffFamily.AEEq Fcanon F :=
    mainInsertionTriadicCoeffFamily_aeeq M m t ω ht hlocal
  have hmaxEq (k : ℤ) :
      maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q k a =
        Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F := by
    unfold maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
    rw [dite_eq_left hlocal]
    exact Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_eq_ofAEEq hAEEq Q k
  let A : CoeffField 2 :=
    Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hEll : IsEllipticFieldOn M.nu (F.coeffOn Q).Lam (openCubeSet Q) A := by
    simpa [A, F, mainInsertionTriadicCoeffFamily, mainInsertionCoeffOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using Ch02.pointwiseCoeffField_openCube_descendant_data Q (F.coeffOn Q)
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hmatrix :=
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
      F Q hk
  have hblock :
      maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) A ≤ 8 * M.nu⁻¹ := by
    have hraw :=
      Homogenization.maxDescendantSigmaStarInvNormAtScale_le_uniform_of_isEllipticFieldOn_openCubeSet_of_openCubeDescendantDeterministicCoarseData
        Q A hEll hData n
    have hdim : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
    rw [hdim] at hraw
    calc
      maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) A ≤
          4 * 2 * M.nu⁻¹ := hraw
      _ = 8 * M.nu⁻¹ := by ring
  rw [hmaxEq]
  exact hmatrix.trans hblock

private theorem mainInsertion_qone_tsum_le_const
    {H : ℕ → ℝ} {s C : ℝ} (hs : 0 < s)
    (hH_nonneg : ∀ n : ℕ, 0 ≤ H n) (hH_le : ∀ n : ℕ, H n ≤ C) :
    (∑' n : ℕ, Ch02.geometricWeight s 1 n * H n) ≤ C := by
  have hs1 : 0 < s * (1 : ℝ) := by simpa using hs
  have hsumH : Summable (fun n : ℕ => Ch02.geometricWeight s 1 n * H n) :=
    Homogenization.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s) (q := 1) (C := C) hs1 hH_nonneg hH_le
  have hsumC : Summable (fun n : ℕ => Ch02.geometricWeight s 1 n * C) :=
    (Homogenization.summable_geometricWeight (s := s) (q := 1) hs1).mul_right C
  have hterm : ∀ n : ℕ, Ch02.geometricWeight s 1 n * H n ≤
      Ch02.geometricWeight s 1 n * C := by
    intro n
    exact mul_le_mul_of_nonneg_left (hH_le n)
      (Homogenization.geometricWeight_nonneg n hs1.le)
  calc
    (∑' n : ℕ, Ch02.geometricWeight s 1 n * H n) ≤
        ∑' n : ℕ, Ch02.geometricWeight s 1 n * C :=
      Summable.tsum_le_tsum hterm hsumH hsumC
    _ = C := by
      rw [tsum_mul_right]
      have hweight : (∑' n : ℕ, Ch02.geometricWeight s 1 n) = 1 := by
        simpa [Ch02.geometricWeight_eq_old] using
          (Homogenization.tsum_geometricWeight_eq_one hs1)
      rw [hweight, one_mul]

private theorem mainInsertion_measurableSet_aeLocallyUniformlyEllipticField :
    MeasurableSet
      {a : RegCoeffField 2 | AELocallyUniformlyEllipticField a} := by
  classical
  have hEq :
      {a : RegCoeffField 2 | AELocallyUniformlyEllipticField a} =
        ⋂ Q : TriadicCube 2, ⋃ k : ℕ,
          {a : RegCoeffField 2 |
            AEEQuantitativeEllipticSlice (cubeSet Q) k a.toFun} := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    constructor
    · intro ha Q
      exact ha.exists_aeeQuantitativeEllipticSlice_cubeSet Q
    · intro ha Q
      obtain ⟨k, hk⟩ := ha Q
      have hkpos : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
      have h1le : (1 : ℝ) ≤ (k : ℝ) + 1 := by
        have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      have hle : ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 :=
        le_trans ((inv_le_one₀ (by positivity)).2 h1le) h1le
      refine ⟨((k : ℝ) + 1)⁻¹, (k : ℝ) + 1, hkpos, hle, ?_⟩
      have hslice : IsAEEllipticFieldOn ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)
          (cubeSet Q) a.toFun := hk
      exact hslice.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  rw [hEq]
  refine MeasurableSet.iInter fun Q => MeasurableSet.iUnion fun k => ?_
  exact LocalSigmaR_le (cubeSet Q) _
    (measurableSet_localSigmaR_aeeQuantitativeEllipticSlice Q k)

/-- The law of the actual old-frame coefficient after inserting the fresh
shell with parameter `t`. -/
noncomputable def mainInsertionCoefficientLaw (M : ABKModel 2) (m : ℤ) (t : ℝ) :
    RestrictionCoeffLaw 2 :=
  Measure.map (Model.partialInsertedCoefficient M m t)
    (Cutoff.cutoffSampleLaw M).toMeasure

/-- The sample-to-coefficient map for the partial insertion is measurable. -/
theorem mainInsertion_partialInsertedCoefficient_measurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) :
    Measurable (Model.partialInsertedCoefficient M m t) := by
  have hFresh : Measurable
      (fun ω : Cutoff.CutoffSample 2 =>
        ShellField.forgetShell (ω.1 (m + 1))) :=
    ShellField.measurable_forgetShell.comp
      ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have hScaled : Measurable
      (fun ω : Cutoff.CutoffSample 2 =>
        Real.sqrt t • ShellField.forgetShell (ω.1 (m + 1))) := by
    have hsmul : Measurable
        (fun a : RegCoeffField 2 => Real.sqrt t • a) := by
      refine measurable_into_regCoeffField' ?_ ?_
      · intro x i j
        exact (measurable_apply_entry x i j).const_smul (Real.sqrt t)
      · intro i j φ hφ
        have hfun :
            (fun a : RegCoeffField 2 => entryTestR i j φ (Real.sqrt t • a)) =
              fun a => Real.sqrt t * entryTestR i j φ a := by
          funext a
          exact entryTestR_smul i j (Real.sqrt t) a
        rw [hfun]
        exact (measurable_entryTestR i j hφ).const_mul (Real.sqrt t)
    exact hsmul.comp hFresh
  change Measurable (fun ω : Cutoff.CutoffSample 2 =>
    Cutoff.coefficientCutoff M.nu m ω +
      Real.sqrt t • ShellField.forgetShell (ω.1 (m + 1)))
  exact (Cutoff.measurable_coefficientCutoff M.nu m).add hScaled

/-- The actual partial-insertion coefficient law is a Chapter 4 law carrier.
For each observation cube, the old and fresh local controls give a finite
upper ellipticity constant while the symmetric part remains `M.nu`. -/
theorem mainInsertionCoefficientLaw_lawCarrier
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    RestrictionLawCarrier (mainInsertionCoefficientLaw M m t) := by
  let hcoeff := mainInsertion_partialInsertedCoefficient_measurable M m t
  have hfield (ω : Cutoff.CutoffSample 2) :
      AELocallyUniformlyEllipticField (Model.partialInsertedCoefficient M m t ω) := by
    intro Q
    let ell : ℤ := cubeOriginCoverScale Q
    have hEll : IsEllipticFieldOn M.nu
        ((2 * 2 * Model.partialInsertedEntryBound M ell m ω ^ 2 + M.nu ^ 2) / M.nu)
        (openCubeSet Q)
        (Model.partialInsertedCoefficient M m t ω).toFun := by
      exact Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
        (measurableSet_openCubeSet Q)
        (by
          simpa [ell] using openCubeSet_subset_originCover Q)
    have hEllA : IsAEEllipticFieldOn M.nu
        ((2 * 2 * Model.partialInsertedEntryBound M ell m ω ^ 2 + M.nu ^ 2) / M.nu)
        (openCubeSet Q)
        (Model.partialInsertedCoefficient M m t ω).toFun :=
      IsAEEllipticFieldOn.of_isEllipticFieldOn hEll
    have hnu : M.nu ≤
        (2 * 2 * Model.partialInsertedEntryBound M ell m ω ^ 2 + M.nu ^ 2) / M.nu := by
      apply (le_div_iff₀ M.nu_pos).2
      nlinarith [sq_nonneg (Model.partialInsertedEntryBound M ell m ω)]
    exact ⟨M.nu,
      (2 * 2 * Model.partialInsertedEntryBound M ell m ω ^ 2 + M.nu ^ 2) / M.nu,
      M.nu_pos, hnu, hEllA⟩
  have hLaw : AELocallyUniformlyEllipticLaw (mainInsertionCoefficientLaw M m t) := by
    rw [AELocallyUniformlyEllipticLaw, mainInsertionCoefficientLaw]
    rw [ae_map_iff hcoeff.aemeasurable
      mainInsertion_measurableSet_aeLocallyUniformlyEllipticField]
    exact Filter.Eventually.of_forall hfield
  have hprob : IsProbabilityMeasure (mainInsertionCoefficientLaw M m t) :=
    (Measure.isProbabilityMeasure_map_iff hcoeff.aemeasurable).2 inferInstance
  exact @lawCarrier_of_aeLocallyUniformlyElliptic 2
    (mainInsertionCoefficientLaw M m t) hprob hLaw

private theorem mainInsertion_LambdaSqCoeffField_le_envelope
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : 0 ≤ t ∧ t ≤ 1) (Q : TriadicCube 2) {s : ℝ} (hs : 0 < s) :
    LambdaSqCoeffField Q s (.finite 1) (Model.partialInsertedCoefficient M m t ω) ≤
      8 * M.nu⁻¹ *
        (((2 : ℝ) * 2 * Model.partialInsertedEntryBound M
          (cubeOriginCoverScale Q) m ω ^ 2 + M.nu ^ 2) / M.nu) ^ 2 := by
  let a := Model.partialInsertedCoefficient M m t ω
  let F := mainInsertionTriadicCoeffFamily M m t ω ht
  let hlocal := mainInsertion_partialCoefficient_aelocallyUniformlyElliptic M m t ω ht
  let Fcanon := triadicCoeffFamilyOfAELocallyUniformlyEllipticField a hlocal
  have hAEEq : Ch02.TriadicCoeffFamily.AEEq Fcanon F :=
    mainInsertionTriadicCoeffFamily_aeeq M m t ω ht hlocal
  have hmaxEq (k : ℤ) :
      maxDescendantBMatrixNormCoeffFieldAtScale Q k a =
        Ch02.maxDescendantBMatrixNormAtScale Q k F := by
    unfold maxDescendantBMatrixNormCoeffFieldAtScale
    rw [dite_eq_left hlocal]
    exact Ch02.maxDescendantBMatrixNormAtScale_eq_ofAEEq hAEEq Q k
  have hnonneg : ∀ n : ℕ,
      0 ≤ Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F := by
    intro n
    exact Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F
  have hbound : ∀ n : ℕ,
      Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F ≤
        8 * M.nu⁻¹ *
          (((2 : ℝ) * 2 * Model.partialInsertedEntryBound M
            (cubeOriginCoverScale Q) m ω ^ 2 + M.nu ^ 2) / M.nu) ^ 2 := by
    intro n
    rw [← hmaxEq]
    exact mainInsertion_maxDescendantBMatrixNorm_le M m t ω ht Q n
  calc
    LambdaSqCoeffField Q s (.finite 1) a ≤
        ∑' n : ℕ, Ch02.geometricWeight s 1 n *
          maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a :=
      LambdaSqCoeffField_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale
        Q a hs
    _ = ∑' n : ℕ, Ch02.geometricWeight s 1 n *
          Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F := by
      congr 1
      funext n
      rw [hmaxEq]
    _ ≤ 8 * M.nu⁻¹ *
          (((2 : ℝ) * 2 * Model.partialInsertedEntryBound M
            (cubeOriginCoverScale Q) m ω ^ 2 + M.nu ^ 2) / M.nu) ^ 2 :=
      mainInsertion_qone_tsum_le_const hs hnonneg hbound

private theorem mainInsertion_lambdaSqCoeffField_inv_le_coercivity
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : 0 ≤ t ∧ t ≤ 1) (Q : TriadicCube 2) {s : ℝ} (hs : 0 < s) :
    (lambdaSqCoeffField Q s (.finite 1)
      (Model.partialInsertedCoefficient M m t ω))⁻¹ ≤ 8 * M.nu⁻¹ := by
  let a := Model.partialInsertedCoefficient M m t ω
  let F := mainInsertionTriadicCoeffFamily M m t ω ht
  let hlocal := mainInsertion_partialCoefficient_aelocallyUniformlyElliptic M m t ω ht
  let Fcanon := triadicCoeffFamilyOfAELocallyUniformlyEllipticField a hlocal
  have hAEEq : Ch02.TriadicCoeffFamily.AEEq Fcanon F :=
    mainInsertionTriadicCoeffFamily_aeeq M m t ω ht hlocal
  have hmaxEq (k : ℤ) :
      maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q k a =
        Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k F := by
    unfold maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
    rw [dite_eq_left hlocal]
    exact Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_eq_ofAEEq hAEEq Q k
  have hnonneg : ∀ n : ℕ,
      0 ≤ Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) F := by
    intro n
    exact Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F
  have hbound : ∀ n : ℕ,
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) F ≤ 8 * M.nu⁻¹ := by
    intro n
    rw [← hmaxEq]
    exact mainInsertion_maxDescendantSigmaStarInvMatrixNorm_le M m t ω ht Q n
  calc
    (lambdaSqCoeffField Q s (.finite 1) a)⁻¹ ≤
        ∑' n : ℕ, Ch02.geometricWeight s 1 n *
          maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q
            (Q.scale - (n : ℤ)) a :=
      lambdaSqCoeffField_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
        Q a hs
    _ = ∑' n : ℕ, Ch02.geometricWeight s 1 n *
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) F := by
      congr 1
      funext n
      rw [hmaxEq]
    _ ≤ 8 * M.nu⁻¹ := mainInsertion_qone_tsum_le_const hs hnonneg hbound

/-- The actual partial-insertion law has an integrable upper factor observable.
The random ellipticity envelope is controlled by the proved fourth moment of
the partial-insertion entry bound. -/
theorem mainInsertionCoefficientLaw_integrable_LambdaSqCoeffField
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (Q : TriadicCube 2) :
    Integrable (fun a : RegCoeffField 2 =>
      LambdaSqCoeffField Q 1 (.finite 1) a) (mainInsertionCoefficientLaw M m t) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let P := mainInsertionCoefficientLaw M m t
  let f : Cutoff.CutoffSample 2 → RegCoeffField 2 :=
    Model.partialInsertedCoefficient M m t
  let E : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    Model.partialInsertedEntryBound M (cubeOriginCoverScale Q) m ω
  let D : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    8 * M.nu⁻¹ * ((32 * E ω ^ 4 + 2 * M.nu ^ 4) / M.nu ^ 2)
  have hf : Measurable f := mainInsertion_partialInsertedCoefficient_measurable M m t
  have hP : RestrictionLawCarrier P := mainInsertionCoefficientLaw_lawCarrier M m t ht
  have hFactor : AEMeasurable
      (fun a : RegCoeffField 2 => LambdaSqCoeffField Q 1 (.finite 1) a) P :=
    hP.aemeasurable_LambdaSqCoeffField_finite_one Q (by norm_num)
  have hFactorSample : AEMeasurable
      (fun ω : Cutoff.CutoffSample 2 => LambdaSqCoeffField Q 1 (.finite 1) (f ω)) μ :=
    hFactor.comp_aemeasurable hf.aemeasurable
  have hE4 : Integrable (fun ω => E ω ^ 4) μ := by
    simpa [E] using mainInsertion_partialEntryBound_fourth_integrable
      M (cubeOriginCoverScale Q) m
  have hsum : Integrable (fun ω => 32 * E ω ^ 4 + 2 * M.nu ^ 4) μ := by
    have hleft := hE4.const_mul 32
    have hright : Integrable (fun _ : Cutoff.CutoffSample 2 => 2 * M.nu ^ 4) μ :=
      integrable_const _
    convert hleft.add hright using 1
  have hinner : Integrable
      (fun ω => (32 * E ω ^ 4 + 2 * M.nu ^ 4) / M.nu ^ 2) μ := by
    convert hsum.const_mul (M.nu ^ 2)⁻¹ using 1
    ext ω
    simp [div_eq_mul_inv, mul_comm]
  have hD : Integrable D μ := by
    convert hinner.const_mul (8 * M.nu⁻¹) using 1
  have hEllBound : ∀ ω,
      8 * M.nu⁻¹ *
          (((2 : ℝ) * 2 * E ω ^ 2 + M.nu ^ 2) / M.nu) ^ 2 ≤ D ω := by
    intro ω
    have hnum : ((2 : ℝ) * 2 * E ω ^ 2 + M.nu ^ 2) ^ 2 ≤
        32 * E ω ^ 4 + 2 * M.nu ^ 4 := by
      nlinarith [sq_nonneg (4 * E ω ^ 2 - M.nu ^ 2)]
    have hdiv : (((2 : ℝ) * 2 * E ω ^ 2 + M.nu ^ 2) / M.nu) ^ 2 ≤
        (32 * E ω ^ 4 + 2 * M.nu ^ 4) / M.nu ^ 2 := by
      rw [div_pow]
      apply (div_le_div_iff₀ (sq_pos_of_pos M.nu_pos)
        (sq_pos_of_pos M.nu_pos)).2
      exact mul_le_mul_of_nonneg_right hnum (sq_nonneg M.nu)
    exact mul_le_mul_of_nonneg_left hdiv
      (mul_nonneg (by norm_num) (inv_nonneg.mpr M.nu_pos.le))
  have hFactorIntSample : Integrable
      (fun ω => LambdaSqCoeffField Q 1 (.finite 1) (f ω)) μ := by
    refine hD.mono' hFactorSample.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs,
      abs_of_nonneg (LambdaSqCoeffField_finite_nonneg Q (f ω) (by norm_num)
        (by norm_num : (1 : ℝ) ≤ 1))]
    calc
      LambdaSqCoeffField Q 1 (.finite 1) (f ω) ≤
          8 * M.nu⁻¹ *
            (((2 : ℝ) * 2 * Model.partialInsertedEntryBound M
              (cubeOriginCoverScale Q) m ω ^ 2 + M.nu ^ 2) / M.nu) ^ 2 :=
        mainInsertion_LambdaSqCoeffField_le_envelope M m t ω ht Q
          (by norm_num : (0 : ℝ) < 1)
      _ ≤ D ω := by simpa [D, E] using hEllBound ω
  have hFactorSampleMap : Integrable
      (fun a : RegCoeffField 2 => LambdaSqCoeffField Q 1 (.finite 1) a) P := by
    apply (integrable_map_measure hFactor.aestronglyMeasurable hf.aemeasurable).mpr
    change Integrable
      ((fun a : RegCoeffField 2 => LambdaSqCoeffField Q 1 (.finite 1) a) ∘ f) μ
    exact hFactorIntSample
  exact hFactorSampleMap

/-- The lower inverse factor for the partial-insertion law is bounded by the
fixed molecular coercivity, so it is integrable without an upper-tail input. -/
theorem mainInsertionCoefficientLaw_integrable_lambdaSqCoeffField_inv
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (Q : TriadicCube 2) :
    Integrable (fun a : RegCoeffField 2 =>
      (lambdaSqCoeffField Q 1 (.finite 1) a)⁻¹) (mainInsertionCoefficientLaw M m t) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let P := mainInsertionCoefficientLaw M m t
  let f : Cutoff.CutoffSample 2 → RegCoeffField 2 :=
    Model.partialInsertedCoefficient M m t
  have hf : Measurable f := mainInsertion_partialInsertedCoefficient_measurable M m t
  have hP : RestrictionLawCarrier P := mainInsertionCoefficientLaw_lawCarrier M m t ht
  have hFactor : AEMeasurable
      (fun a : RegCoeffField 2 => (lambdaSqCoeffField Q 1 (.finite 1) a)⁻¹) P :=
    hP.aemeasurable_lambdaSqCoeffField_finite_one_inv Q (by norm_num)
  have hFactorSample : AEMeasurable
      (fun ω : Cutoff.CutoffSample 2 =>
        (lambdaSqCoeffField Q 1 (.finite 1) (f ω))⁻¹) μ :=
    hFactor.comp_aemeasurable hf.aemeasurable
  have hFactorIntSample : Integrable
      (fun ω => (lambdaSqCoeffField Q 1 (.finite 1) (f ω))⁻¹) μ := by
    refine (integrable_const (8 * M.nu⁻¹)).mono' hFactorSample.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr
      (lambdaSqCoeffField_finite_nonneg Q (f ω) (by norm_num)
        (by norm_num : (1 : ℝ) ≤ 1)))]
    exact mainInsertion_lambdaSqCoeffField_inv_le_coercivity M m t ω ht Q
      (by norm_num : (0 : ℝ) < 1)
  apply (integrable_map_measure hFactor.aestronglyMeasurable hf.aemeasurable).mpr
  change Integrable
    ((fun a : RegCoeffField 2 => (lambdaSqCoeffField Q 1 (.finite 1) a)⁻¹) ∘ f) μ
  exact hFactorIntSample

/-- The actual partial-insertion coarse full block matrix is integrable at each
observation cube under its source law. -/
theorem mainInsertionCoefficientLaw_integrable_coarseFullBlockMatrixAtCube
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (Q : TriadicCube 2) :
    Integrable (coarseFullBlockMatrixAtCube Q) (mainInsertionCoefficientLaw M m t) := by
  let P := mainInsertionCoefficientLaw M m t
  have hP : RestrictionLawCarrier P := mainInsertionCoefficientLaw_lawCarrier M m t ht
  have hUpper : Integrable
      (fun a : RegCoeffField 2 => (LambdaSqCoeffField Q 1 (.finite 1) a) ^ 1) P := by
    simpa [P, pow_one] using mainInsertionCoefficientLaw_integrable_LambdaSqCoeffField M m t ht Q
  have hLower : Integrable
      (fun a : RegCoeffField 2 => ((lambdaSqCoeffField Q 1 (.finite 1) a)⁻¹) ^ 1) P := by
    simpa [P, pow_one] using mainInsertionCoefficientLaw_integrable_lambdaSqCoeffField_inv M m t ht Q
  exact hP.integrable_coarseFullBlockMatrixAtCube_of_integrable_factor_observables Q
    (by norm_num) (by norm_num) (by norm_num : 1 ≤ 1) hUpper hLower

/-- Each full block-matrix entry is integrable under the actual partial-
insertion coefficient law. -/
theorem mainInsertionCoefficientLaw_integrable_blockMatEntry
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (Q : TriadicCube 2) (α β : BlockCoord 2) :
    Integrable
      (fun a : RegCoeffField 2 =>
        blockMatEntry (coarseBlockMatrix (cubeSet Q) a.toFun) α β)
      (mainInsertionCoefficientLaw M m t) :=
  Ch04.RestrictionLawCarrier.integrable_blockMatEntry_coarseBlockMatrix_cubeSet_of_integrable_coarseFullBlockMatrixAtCube
    (mainInsertionCoefficientLaw_integrable_coarseFullBlockMatrixAtCube M m t ht Q) α β

/-- Every entry of the actual partial-insertion coarse matrix is integrable on
the sample carrier, not just a.e.-measurable. -/
theorem mainInsertion_coarseBlockMatrix_entry_integrable
    (M : ABKModel 2) (m n : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (α β : BlockCoord 2) :
    Integrable
      (fun ω : Cutoff.CutoffSample 2 =>
        blockMatEntry
          (coarseBlockMatrix (cubeSet (originCube 2 n))
            (Model.partialInsertedCoefficient M m t ω).toFun) α β)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f : Cutoff.CutoffSample 2 → RegCoeffField 2 :=
    Model.partialInsertedCoefficient M m t
  let g : RegCoeffField 2 → ℝ := fun a =>
    blockMatEntry (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun) α β
  have hf : Measurable f := mainInsertion_partialInsertedCoefficient_measurable M m t
  have hLaw : Integrable g (mainInsertionCoefficientLaw M m t) := by
    exact Ch04.RestrictionLawCarrier.integrable_blockMatEntry_coarseBlockMatrix_cubeSet_of_integrable_coarseFullBlockMatrixAtCube
      (mainInsertionCoefficientLaw_integrable_coarseFullBlockMatrixAtCube M m t ht
        (originCube 2 n)) α β
  have hInt := (integrable_map_measure hLaw.aestronglyMeasurable hf.aemeasurable).mp hLaw
  change Integrable (g ∘ f) μ
  exact hInt

private theorem mainInsertion_integral_rotation_sample
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (R : Mat 2)
    (hR : IsSignedPermutationMatrix R) (g : RegCoeffField 2 → ℝ)
    (hg : AEStronglyMeasurable g (mainInsertionCoefficientLaw M m t)) :
    ∫ ω, g (Model.partialInsertedCoefficient M m t ω) ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      ∫ ω, g (Model.rotateCoefficientAbout (0 : Vec 2) R hR
        (Model.partialInsertedCoefficient M m t ω))
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let P := mainInsertionCoefficientLaw M m t
  let f : Cutoff.CutoffSample 2 → RegCoeffField 2 :=
    Model.partialInsertedCoefficient M m t
  let rotate : RegCoeffField 2 → RegCoeffField 2 :=
    Model.rotateCoefficientAbout (0 : Vec 2) R hR
  have hf : Measurable f := mainInsertion_partialInsertedCoefficient_measurable M m t
  have hrotate : Measurable rotate := by
    change Measurable (Model.rotateCoefficientAbout (0 : Vec 2) R hR)
    exact (measurable_translateReg (-(0 : Vec 2))).comp
      ((measurable_rotateReg R hR).comp (measurable_translateReg (0 : Vec 2)))
  have hrotf : Measurable (rotate ∘ f) := hrotate.comp hf
  have hrotMap : Measure.map (rotate ∘ f) μ = P := by
    change Measure.map (fun ω => Model.rotateCoefficientAbout (0 : Vec 2) R hR
      (Model.partialInsertedCoefficient M m t ω)) μ = P
    simpa [μ, P, mainInsertionCoefficientLaw, f, rotate] using
      mainInsertion_coefficient_rotation_law M m t (0 : Vec 2) R hR
  have hbase :
      ∫ a, g a ∂P = ∫ ω, g (f ω) ∂μ := by
    change ∫ a, g a ∂(Measure.map f μ) = _
    exact integral_map hf.aemeasurable hg
  have hrot :
      ∫ a, g a ∂P = ∫ ω, g ((rotate ∘ f) ω) ∂μ := by
    rw [← hrotMap]
    exact integral_map hrotf.aemeasurable (hrotMap ▸ hg)
  exact hbase.symm.trans hrot

private theorem mainInsertionCoefficientLaw_integral_zero_of_signFlip
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (g : RegCoeffField 2 → ℝ)
    (hg : Integrable g (mainInsertionCoefficientLaw M m t))
    (R : Mat 2) (hR : IsSignedPermutationMatrix R)
    (hneg : ∀ ω : Cutoff.CutoffSample 2,
      g (Model.rotateCoefficientAbout (0 : Vec 2) R hR
        (Model.partialInsertedCoefficient M m t ω)) =
          -g (Model.partialInsertedCoefficient M m t ω)) :
    ∫ a, g a ∂mainInsertionCoefficientLaw M m t = 0 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let P := mainInsertionCoefficientLaw M m t
  let f : Cutoff.CutoffSample 2 → RegCoeffField 2 :=
    Model.partialInsertedCoefficient M m t
  have hf : Measurable f := mainInsertion_partialInsertedCoefficient_measurable M m t
  have hbase : ∫ a, g a ∂P = ∫ ω, g (f ω) ∂μ := by
    change ∫ a, g a ∂(Measure.map f μ) = _
    exact integral_map hf.aemeasurable hg.aestronglyMeasurable
  have hrot := mainInsertion_integral_rotation_sample M m t R hR g
    hg.aestronglyMeasurable
  have hrotNeg :
      ∫ ω, g (Model.rotateCoefficientAbout (0 : Vec 2) R hR (f ω)) ∂μ =
        -(∫ ω, g (f ω) ∂μ) := by
    calc
      ∫ ω, g (Model.rotateCoefficientAbout (0 : Vec 2) R hR (f ω)) ∂μ =
          ∫ ω, -g (f ω) ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hneg
      _ = -(∫ ω, g (f ω) ∂μ) := by rw [integral_neg]
  have hI : ∫ a, g a ∂P = -(∫ a, g a ∂P) := by
    calc
      ∫ a, g a ∂P = ∫ ω, g (f ω) ∂μ := hbase
      _ = ∫ ω, g (Model.rotateCoefficientAbout (0 : Vec 2) R hR (f ω)) ∂μ := hrot
      _ = -(∫ ω, g (f ω) ∂μ) := hrotNeg
      _ = -(∫ a, g a ∂P) := by rw [hbase]
  linarith

/-- Signed-permutation invariance forces the diagonal upper-left response
means of the actual insertion law to agree. -/
theorem mainInsertionCoefficientLaw_upperLeft_diagonal_mean_eq
    (M : ABKModel 2) (m n : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    ∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).upperLeft 0 0 ∂
        mainInsertionCoefficientLaw M m t =
      ∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).upperLeft 1 1 ∂
        mainInsertionCoefficientLaw M m t := by
  let Q := originCube 2 n
  let P := mainInsertionCoefficientLaw M m t
  let g0 : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (openCubeSet Q) a.toFun).upperLeft 0 0
  let g1 : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (openCubeSet Q) a.toFun).upperLeft 1 1
  have hInt0 : Integrable g0 P := by
    have hentry := mainInsertionCoefficientLaw_integrable_blockMatEntry
      M m t ht Q (Sum.inl 0) (Sum.inl 0)
    simpa [g0, Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using hentry
  have hInt1 : Integrable g1 P := by
    have hentry := mainInsertionCoefficientLaw_integrable_blockMatEntry
      M m t ht Q (Sum.inl 1) (Sum.inl 1)
    simpa [g1, Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using hentry
  have hrot := mainInsertion_integral_rotation_sample M m t (Matrix.swap ℝ 0 1)
    (isSignedPermutationMatrix_swap 0 1) g0 hInt0.aestronglyMeasurable
  have hpoint (ω : Cutoff.CutoffSample 2) :
      g0 (Model.rotateCoefficientAbout (0 : Vec 2) (Matrix.swap ℝ 0 1)
          (isSignedPermutationMatrix_swap 0 1)
          (Model.partialInsertedCoefficient M m t ω)) =
        g1 (Model.partialInsertedCoefficient M m t ω) := by
    have hmat := mainInsertion_coarseBlockMatrix_swap M m n t ω ht 0 1
    have hentry := congrArg (fun B : BlockMat 2 => B.upperLeft 0 0) hmat
    simpa [g0, g1, Q, Homogenization.blockMatConj, Matrix.mul_apply,
      Matrix.swap] using hentry
  have hpointInt :
      ∫ ω, g0 (Model.rotateCoefficientAbout (0 : Vec 2) (Matrix.swap ℝ 0 1)
        (isSignedPermutationMatrix_swap 0 1)
        (Model.partialInsertedCoefficient M m t ω))
        ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      ∫ ω, g1 (Model.partialInsertedCoefficient M m t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpoint
  have hbase0 :
      ∫ a, g0 a ∂P =
        ∫ ω, g0 (Model.partialInsertedCoefficient M m t ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    change ∫ a, g0 a ∂(Measure.map (Model.partialInsertedCoefficient M m t)
      (Cutoff.cutoffSampleLaw M).toMeasure) = _
    exact integral_map
      (mainInsertion_partialInsertedCoefficient_measurable M m t).aemeasurable
      hInt0.aestronglyMeasurable
  have hbase1 :
      ∫ a, g1 a ∂P =
        ∫ ω, g1 (Model.partialInsertedCoefficient M m t ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    change ∫ a, g1 a ∂(Measure.map (Model.partialInsertedCoefficient M m t)
      (Cutoff.cutoffSampleLaw M).toMeasure) = _
    exact integral_map
      (mainInsertion_partialInsertedCoefficient_measurable M m t).aemeasurable
      hInt1.aestronglyMeasurable
  calc
    ∫ a, (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft 0 0 ∂P =
        ∫ a, g0 a ∂P := by
          simp [g0, Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
    _ = ∫ ω, g0 (Model.partialInsertedCoefficient M m t ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := hbase0
    _ = ∫ ω, g0 (Model.rotateCoefficientAbout (0 : Vec 2) (Matrix.swap ℝ 0 1)
          (isSignedPermutationMatrix_swap 0 1)
          (Model.partialInsertedCoefficient M m t ω))
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := hrot
    _ = ∫ ω, g1 (Model.partialInsertedCoefficient M m t ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := hpointInt
    _ = ∫ a, g1 a ∂P := hbase1.symm
    _ = ∫ a, (coarseBlockMatrix (cubeSet Q) a.toFun).upperLeft 1 1 ∂P := by
          simp [g1, Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]

/-- The lower-right inverse-response block has equal diagonal means under the
actual partial-insertion law. -/
theorem mainInsertionCoefficientLaw_lowerRight_diagonal_mean_eq
    (M : ABKModel 2) (m n : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    ∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).lowerRight 0 0 ∂
        mainInsertionCoefficientLaw M m t =
      ∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).lowerRight 1 1 ∂
        mainInsertionCoefficientLaw M m t := by
  let Q := originCube 2 n
  let P := mainInsertionCoefficientLaw M m t
  let g0 : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (openCubeSet Q) a.toFun).lowerRight 0 0
  let g1 : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (openCubeSet Q) a.toFun).lowerRight 1 1
  have hInt0 : Integrable g0 P := by
    have hentry := mainInsertionCoefficientLaw_integrable_blockMatEntry
      M m t ht Q (Sum.inr 0) (Sum.inr 0)
    simpa [g0, Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using hentry
  have hInt1 : Integrable g1 P := by
    have hentry := mainInsertionCoefficientLaw_integrable_blockMatEntry
      M m t ht Q (Sum.inr 1) (Sum.inr 1)
    simpa [g1, Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using hentry
  have hrot := mainInsertion_integral_rotation_sample M m t (Matrix.swap ℝ 0 1)
    (isSignedPermutationMatrix_swap 0 1) g0 hInt0.aestronglyMeasurable
  have hpoint (ω : Cutoff.CutoffSample 2) :
      g0 (Model.rotateCoefficientAbout (0 : Vec 2) (Matrix.swap ℝ 0 1)
          (isSignedPermutationMatrix_swap 0 1)
          (Model.partialInsertedCoefficient M m t ω)) =
        g1 (Model.partialInsertedCoefficient M m t ω) := by
    have hmat := mainInsertion_coarseBlockMatrix_swap M m n t ω ht 0 1
    have hentry := congrArg (fun B : BlockMat 2 => B.lowerRight 0 0) hmat
    simpa [g0, g1, Q, Homogenization.blockMatConj, Matrix.mul_apply,
      Matrix.swap] using hentry
  have hpointInt :
      ∫ ω, g0 (Model.rotateCoefficientAbout (0 : Vec 2) (Matrix.swap ℝ 0 1)
        (isSignedPermutationMatrix_swap 0 1)
        (Model.partialInsertedCoefficient M m t ω))
        ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      ∫ ω, g1 (Model.partialInsertedCoefficient M m t ω)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall hpoint
  have hbase0 :
      ∫ a, g0 a ∂P =
        ∫ ω, g0 (Model.partialInsertedCoefficient M m t ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    change ∫ a, g0 a ∂(Measure.map (Model.partialInsertedCoefficient M m t)
      (Cutoff.cutoffSampleLaw M).toMeasure) = _
    exact integral_map
      (mainInsertion_partialInsertedCoefficient_measurable M m t).aemeasurable
      hInt0.aestronglyMeasurable
  have hbase1 :
      ∫ a, g1 a ∂P =
        ∫ ω, g1 (Model.partialInsertedCoefficient M m t ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
    change ∫ a, g1 a ∂(Measure.map (Model.partialInsertedCoefficient M m t)
      (Cutoff.cutoffSampleLaw M).toMeasure) = _
    exact integral_map
      (mainInsertion_partialInsertedCoefficient_measurable M m t).aemeasurable
      hInt1.aestronglyMeasurable
  calc
    ∫ a, (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight 0 0 ∂P =
        ∫ a, g0 a ∂P := by
          simp [g0, Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]
    _ = ∫ ω, g0 (Model.partialInsertedCoefficient M m t ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := hbase0
    _ = ∫ ω, g0 (Model.rotateCoefficientAbout (0 : Vec 2) (Matrix.swap ℝ 0 1)
          (isSignedPermutationMatrix_swap 0 1)
          (Model.partialInsertedCoefficient M m t ω))
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := hrot
    _ = ∫ ω, g1 (Model.partialInsertedCoefficient M m t ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := hpointInt
    _ = ∫ a, g1 a ∂P := hbase1.symm
    _ = ∫ a, (coarseBlockMatrix (cubeSet Q) a.toFun).lowerRight 1 1 ∂P := by
          simp [g1, Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet]

/-- Every off-diagonal mean in either diagonal response block vanishes under
the actual partial-insertion law. -/
theorem mainInsertionCoefficientLaw_offDiagonalMeans_eq_zero
    (M : ABKModel 2) (m n : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    (∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).upperLeft 0 1 ∂
        mainInsertionCoefficientLaw M m t = 0) ∧
    (∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).upperLeft 1 0 ∂
        mainInsertionCoefficientLaw M m t = 0) ∧
    (∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).lowerRight 0 1 ∂
        mainInsertionCoefficientLaw M m t = 0) ∧
    (∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).lowerRight 1 0 ∂
        mainInsertionCoefficientLaw M m t = 0) := by
  let Q := originCube 2 n
  let P := mainInsertionCoefficientLaw M m t
  let gU' : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (openCubeSet Q) a.toFun).upperLeft 0 1
  let gUL10 : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (openCubeSet Q) a.toFun).upperLeft 1 0
  let gLR01 : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (openCubeSet Q) a.toFun).lowerRight 0 1
  let gLR10 : RegCoeffField 2 → ℝ := fun a =>
    (coarseBlockMatrix (openCubeSet Q) a.toFun).lowerRight 1 0
  have hIntU' : Integrable gU' P := by
    have hentry := mainInsertionCoefficientLaw_integrable_blockMatEntry
      M m t ht Q (Sum.inl 0) (Sum.inl 1)
    simpa [gU', Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using hentry
  have hIntUL10 : Integrable gUL10 P := by
    have hentry := mainInsertionCoefficientLaw_integrable_blockMatEntry
      M m t ht Q (Sum.inl 1) (Sum.inl 0)
    simpa [gUL10, Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using hentry
  have hIntLR01 : Integrable gLR01 P := by
    have hentry := mainInsertionCoefficientLaw_integrable_blockMatEntry
      M m t ht Q (Sum.inr 0) (Sum.inr 1)
    simpa [gLR01, Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using hentry
  have hIntLR10 : Integrable gLR10 P := by
    have hentry := mainInsertionCoefficientLaw_integrable_blockMatEntry
      M m t ht Q (Sum.inr 1) (Sum.inr 0)
    simpa [gLR10, Q, blockMatEntry, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using hentry
  have hPointU (ω : Cutoff.CutoffSample 2) :
      gU' (Model.rotateCoefficientAbout (0 : Vec 2) (signFlipMatrix 0)
          (isSignedPermutationMatrix_signFlipMatrix 0)
          (Model.partialInsertedCoefficient M m t ω)) =
        -gU' (Model.partialInsertedCoefficient M m t ω) := by
    have hmat := mainInsertion_coarseBlockMatrix_signFlip M m n t ω ht 0
    have hentry := congrArg (fun B : BlockMat 2 => B.upperLeft 0 1) hmat
    simpa [gU', Q, Homogenization.blockMatConj, Homogenization.signFlipMatrix,
      Matrix.mul_apply] using hentry
  have hPointUL10 (ω : Cutoff.CutoffSample 2) :
      gUL10 (Model.rotateCoefficientAbout (0 : Vec 2) (signFlipMatrix 0)
          (isSignedPermutationMatrix_signFlipMatrix 0)
          (Model.partialInsertedCoefficient M m t ω)) =
        -gUL10 (Model.partialInsertedCoefficient M m t ω) := by
    have hmat := mainInsertion_coarseBlockMatrix_signFlip M m n t ω ht 0
    have hentry := congrArg (fun B : BlockMat 2 => B.upperLeft 1 0) hmat
    simpa [gUL10, Q, Homogenization.blockMatConj, Homogenization.signFlipMatrix,
      Matrix.mul_apply] using hentry
  have hPointLR01 (ω : Cutoff.CutoffSample 2) :
      gLR01 (Model.rotateCoefficientAbout (0 : Vec 2) (signFlipMatrix 0)
          (isSignedPermutationMatrix_signFlipMatrix 0)
          (Model.partialInsertedCoefficient M m t ω)) =
        -gLR01 (Model.partialInsertedCoefficient M m t ω) := by
    have hmat := mainInsertion_coarseBlockMatrix_signFlip M m n t ω ht 0
    have hentry := congrArg (fun B : BlockMat 2 => B.lowerRight 0 1) hmat
    simpa [gLR01, Q, Homogenization.blockMatConj, Homogenization.signFlipMatrix,
      Matrix.mul_apply] using hentry
  have hPointLR10 (ω : Cutoff.CutoffSample 2) :
      gLR10 (Model.rotateCoefficientAbout (0 : Vec 2) (signFlipMatrix 0)
          (isSignedPermutationMatrix_signFlipMatrix 0)
          (Model.partialInsertedCoefficient M m t ω)) =
        -gLR10 (Model.partialInsertedCoefficient M m t ω) := by
    have hmat := mainInsertion_coarseBlockMatrix_signFlip M m n t ω ht 0
    have hentry := congrArg (fun B : BlockMat 2 => B.lowerRight 1 0) hmat
    simpa [gLR10, Q, Homogenization.blockMatConj, Homogenization.signFlipMatrix,
      Matrix.mul_apply] using hentry
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [gU', Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using
    mainInsertionCoefficientLaw_integral_zero_of_signFlip M m t gU' hIntU'
        (signFlipMatrix 0) (isSignedPermutationMatrix_signFlipMatrix 0) hPointU
  · simpa [gUL10, Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using
    mainInsertionCoefficientLaw_integral_zero_of_signFlip M m t gUL10 hIntUL10
        (signFlipMatrix 0) (isSignedPermutationMatrix_signFlipMatrix 0) hPointUL10
  · simpa [gLR01, Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using
    mainInsertionCoefficientLaw_integral_zero_of_signFlip M m t gLR01 hIntLR01
        (signFlipMatrix 0) (isSignedPermutationMatrix_signFlipMatrix 0) hPointLR01
  · simpa [gLR10, Q, coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet] using
    mainInsertionCoefficientLaw_integral_zero_of_signFlip M m t gLR10 hIntLR10
        (signFlipMatrix 0) (isSignedPermutationMatrix_signFlipMatrix 0) hPointLR10

/-- The expected upper-left and lower-right response blocks are scalar
matrices for the actual partial-insertion law. -/
theorem mainInsertionCoefficientLaw_expectedDiagonalBlocks_areScalar
    (M : ABKModel 2) (m n : ℤ) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    ∃ k d : ℝ,
      (∀ i j : Fin 2,
        ∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).upperLeft i j ∂
          mainInsertionCoefficientLaw M m t = if i = j then k else 0) ∧
      (∀ i j : Fin 2,
        ∫ a, (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).lowerRight i j ∂
          mainInsertionCoefficientLaw M m t = if i = j then d else 0) := by
  let k : ℝ := ∫ a,
    (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).upperLeft 0 0 ∂
      mainInsertionCoefficientLaw M m t
  let d : ℝ := ∫ a,
    (coarseBlockMatrix (cubeSet (originCube 2 n)) a.toFun).lowerRight 0 0 ∂
      mainInsertionCoefficientLaw M m t
  have hdiagUL := mainInsertionCoefficientLaw_upperLeft_diagonal_mean_eq M m n t ht
  have hdiagLR := mainInsertionCoefficientLaw_lowerRight_diagonal_mean_eq M m n t ht
  have hoff := mainInsertionCoefficientLaw_offDiagonalMeans_eq_zero M m n t ht
  refine ⟨k, d, ?_, ?_⟩
  · intro i j
    fin_cases i
    · fin_cases j
      · simp [k]
      · simpa using hoff.1
    · fin_cases j
      · simpa using hoff.2.1
      · simpa [k] using hdiagUL.symm
  · intro i j
    fin_cases i
    · fin_cases j
      · simp [d]
      · simpa using hoff.2.2.1
    · fin_cases j
      · simpa using hoff.2.2.2
      · simpa [d] using hdiagLR.symm

end

end ASDExplicitGamma.Main
