module

public import ASDExplicitGamma.Main.EOscillationJointProfile
public import ASDExplicitGamma.Main.InverseDeficitODE
public import ASDExplicitGamma.Inverse.BankGlobal
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Inverse.PureFluxGeneratorOpenBridge
public import ASDExplicitGamma.Gaussian.ModelHeatLaw
public import ASDExplicitGamma.Main.PartialInsertion
public import ASDExplicitGamma.Native.OldSignedHistoryCongr
public import ASDExplicitGamma.Inverse.ParentGapCenteredDepth

/-! The first-shell global bank rooted on the actual q3 source square supplies
the source coefficient's inverse history in the same OLD frame. -/

@[expose] public section

namespace ASDExplicitGamma.Main

attribute [local irreducible] Homogenization.descendantsAtDepth

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Native ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open scoped ENNReal

noncomputable section

/-- The single source-square root used by the actual OLD oscillation row. -/
noncomputable def mainCutoffQ3SourceInverseBankMax
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  bankFiniteRootHistoryMax
    ({originCube 2 (m - 5)} : Finset (TriadicCube 2)) M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω

private theorem main_q3_source_inverse_history_frame_scale
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ Lam : ℝ,
      IsEllipticFieldOn M.nu Lam (openCubeSet (originCube 2 (m - 5)))
        (Model.partialInsertedCoefficient M (m + (1 : ℤ) - 1) t ω).toFun ∧
      lemmaVInverseHistory (originCube 2 (m - 5))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (pureFluxOpenResponseRestriction m
            (modelInsertedScalar (closure (cubeSet (originCube 2 m)))
              (m + (1 : ℤ) - 1) t ω))) ((3 : ℝ) ^ (1 / 4 : ℝ)) =
        (Annealed.sigmaBar M m : ℝ) * lemmaVInverseHistory
          (originCube 2 (m - 5))
          ((Model.partialInsertedCoefficient M (m + (1 : ℤ) - 1) t ω).toFun)
          ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let P : TriadicCube 2 := originCube 2 m
  let σ : ℝ := Annealed.sigmaBar M m
  let K : Set (Vec 2) := closure (cubeSet P)
  have hKcompact : CompactSpace K := by
    dsimp [K, P]
    infer_instance
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet P).isCompact_closure
  have hQdepth : Q ∈ descendantsAtDepth P 5 := by
    change originCube 2 (m - 5) ∈ descendantsAtDepth (originCube 2 m) 5
    exact originCube_mem_descendantsAtDepth' 2 m 5
  let insertionScale : ℤ := m + (1 : ℤ) - 1
  have hinsertionScale : insertionScale = m := by dsimp [insertionScale]; omega
  let f := modelInsertedScalar K insertionScale t ω
  let bankCoeff := pureFluxOpenResponseRestriction m f
  let bankField := responseFramePlanarCoefficientField M.nu σ bankCoeff
  let physicalCoeff :=
    (Model.partialInsertedCoefficient M insertionScale t ω).toFun
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let Lam : ℝ := ((2 : ℝ) * 2 *
    (Model.partialInsertedEntryBound M ell insertionScale ω) ^ 2 + M.nu ^ 2) / M.nu
  have hEllPhysical : IsEllipticFieldOn M.nu Lam (openCubeSet Q) physicalCoeff := by
    have hh := Model.partialInsertedCoefficient_isEllipticFieldOn M ell insertionScale ω
      ⟨ht.1, ht.2⟩ (measurableSet_openCubeSet Q)
      (fun _ hx => hK (subset_closure
        (cubeSet_subset_of_mem_descendantsAtDepth hQdepth
          (openCubeSet_subset_cubeSet Q hx))))
    simpa only [physicalCoeff, Lam] using hh
  have hEllBankRoot : IsEllipticFieldOn (M.nu / σ) _ (openCubeSet P) bankField :=
    responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet P) M.nu σ M.nu_pos hσ bankCoeff
  have hEllBank : IsEllipticFieldOn (M.nu / σ) _ (openCubeSet Q) bankField :=
    hEllBankRoot.mono (measurableSet_openCubeSet Q)
      (openCubeSet_subset_of_mem_descendantsAtDepth hQdepth)
  have hmatrix (R : TriadicCube 2) (j : ℕ)
      (hR : R ∈ descendantsAtDepth Q j) :
      coarseBlockMatrix (cubeSet R) bankField =
        frameMatrix σ (coarseBlockMatrix (cubeSet R) physicalCoeff) := by
    have hR' : R ∈ descendantsAtDepth P (5 + j) := by
      simpa [Nat.add_comm] using mem_descendantsAtDepth_add hQdepth hR
    exact pureFlux_partialInsertion_coarseMatrix_frame m M ell
      (by simpa only [P] using hK) 1 t ω hR'
  have hdepth (j : ℕ) : lemmaVInverseDepthMax Q bankField j =
      σ * lemmaVInverseDepthMax Q physicalCoeff j := by
    rw [← Scalar.inverse_history_framed_depth_max Q physicalCoeff
      hEllPhysical σ hσ j]
    unfold lemmaVInverseDepthMax
    apply Book.Ch02.finsetSupReal_congr
    intro R hR
    have hmatrixR := hmatrix R j hR
    have hlow := congrArg (fun A : BlockMat 2 => A.lowerRight) hmatrixR
    apply congrArg Book.Ch02.matrixNorm
    rw [Scalar.inverse_history_lowerRight R bankField
      (hEllBank.mono (measurableSet_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR))]
    rw [hlow]
    simp [frameMatrix]
  have hhistory : lemmaVInverseHistory Q bankField ((3 : ℝ) ^ (1 / 4 : ℝ)) =
      σ * lemmaVInverseHistory Q physicalCoeff ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
    unfold lemmaVInverseHistory
    simp_rw [hdepth]
    calc
      (1 - ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) *
          ∑' j : ℕ, (((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ j *
            (σ * lemmaVInverseDepthMax Q physicalCoeff j) =
        (1 - ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) *
          (σ * ∑' j : ℕ, (((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ j *
            lemmaVInverseDepthMax Q physicalCoeff j) := by
          congr 1
          calc
            _ = ∑' j : ℕ, σ *
                ((((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ j *
                  lemmaVInverseDepthMax Q physicalCoeff j) := by
                    apply tsum_congr
                    intro j
                    ring
            _ = _ := tsum_mul_left
      _ = σ * ((1 - ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) *
          ∑' j : ℕ, (((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹) ^ j *
            lemmaVInverseDepthMax Q physicalCoeff j) := by ring
  refine ⟨Lam, hEllPhysical, ?_⟩
  simpa only [Q, σ, bankField, bankCoeff, f, physicalCoeff, insertionScale] using hhistory

private theorem main_q3_source_response_coefficient_eq
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    ∀ x ∈ openCubeSet (originCube 2 (m - 5)),
      responseCoefficientExtension
        (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω) x =
      responseCoefficientExtension
        (pureFluxOpenResponseRestriction m
          (modelInsertedScalar (closure (cubeSet (originCube 2 m)))
            (m + (1 : ℤ) - 1) t ω)) x := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let P : TriadicCube 2 := originCube 2 m
  let K : Set (Vec 2) := closure (cubeSet P)
  have hKcompact : CompactSpace K := by
    dsimp [K, P]
    infer_instance
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet P).isCompact_closure
  have hQdepth : Q ∈ descendantsAtDepth P 5 := by
    change originCube 2 (m - 5) ∈ descendantsAtDepth (originCube 2 m) 5
    exact originCube_mem_descendantsAtDepth' 2 m 5
  let insertionScale : ℤ := m + (1 : ℤ) - 1
  have hinsertionScale : insertionScale = m := by dsimp [insertionScale]; omega
  let f := modelInsertedScalar K insertionScale t ω
  let localCoeff := mainInsertionSkewCoefficient m t Q ω
  let bankCoeff := pureFluxOpenResponseRestriction m f
  intro x hx
  have hxP : x ∈ openCubeSet P :=
    openCubeSet_subset_of_mem_descendantsAtDepth hQdepth hx
  have hmodel := modelInsertedScalar_apply K M ell insertionScale hK t ω
    ⟨x, subset_closure (openCubeSet_subset_cubeSet P hxP)⟩
  have hmodelMatrix :
      (Model.partialInsertedCoefficient M insertionScale t ω).toFun x =
        M.nu • (1 : Mat 2) + Cutoff.cutoff insertionScale ω x +
          Real.sqrt t • Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell
            (ω.1 (insertionScale + 1)) x := by
    rw [mainInsertion_coefficient]
    ext i j
    simp [RegCoeffField.add_apply, RegCoeffField.smul_apply,
      Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply]
  have hentry :
      (Model.partialInsertedCoefficient M insertionScale t ω).toFun x 1 0 =
        Cutoff.cutoff insertionScale ω x 1 0 +
          Real.sqrt t * ω.1 (insertionScale + 1) x 1 0 := by
    have hh := congrArg (fun A : Mat 2 => A 1 0) hmodelMatrix
    simpa using hh
  have hmodel' : f ⟨x, subset_closure (openCubeSet_subset_cubeSet P hxP)⟩ =
      Cutoff.cutoff m ω x 1 0 + Real.sqrt t * ω.1 (m + 1) x 1 0 := by
    calc
      _ = (Model.partialInsertedCoefficient M insertionScale t ω).toFun x 1 0 :=
        by simpa only [f] using hmodel
      _ = _ := by simpa only [hinsertionScale] using hentry
  rw [responseCoefficientExtension_eq localCoeff hx,
    pureFluxOpenResponseRestriction_value m f hxP]
  simpa [localCoeff, mainInsertionSkewCoefficient] using hmodel'.symm

private theorem main_q3_source_bank_response_history_le_finite
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2)
    (hfinite : mainCutoffQ3SourceInverseBankMax M m t ω < ∞) :
    oldSignedInverseHistory (originCube 2 (m - 5))
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (pureFluxOpenResponseRestriction m
          (modelInsertedScalar (closure (cubeSet (originCube 2 m)))
            (m + (1 : ℤ) - 1) t ω))) ≤
      (mainCutoffQ3SourceInverseBankMax M m t ω).toReal := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let σ : ℝ := Annealed.sigmaBar M m
  let insertionScale : ℤ := m + (1 : ℤ) - 1
  have hinsertionScale : insertionScale = m := by dsimp [insertionScale]; omega
  let f := modelInsertedScalar (closure (cubeSet (originCube 2 m))) insertionScale t ω
  let bankCoeff := pureFluxOpenResponseRestriction m f
  let bankField := responseFramePlanarCoefficientField M.nu σ bankCoeff
  let physicalCoeff :=
    (Model.partialInsertedCoefficient M insertionScale t ω).toFun
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hcoeff :
      attenuatedCoefficient M m (m + 40)
        (bankPartialInsertionWeights m 1 t) ω = physicalCoeff := by
    funext x
    change attenuatedCoefficient M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω x =
        (Model.partialInsertedCoefficient M insertionScale t ω).toFun x
    rw [bank_partial_insertion_coefficient M m 1 (by omega) t ω x,
      mainInsertion_coefficient]
    simp [RegCoeffField.add_apply, RegCoeffField.smul_apply,
      Algsuperdiff.Frozen.Assumptions.ShellField.forgetShell_apply,
      hinsertionScale]
  obtain ⟨Lam, hEllPhysical, hhistory⟩ :=
    main_q3_source_inverse_history_frame_scale M m t ω ht
  have hroot := bank_root_history_physical Q M m (m + 40)
    (bankPartialInsertionWeights m 1 t) ω physicalCoeff hcoeff hEllPhysical
  have hrootFrame : bankRootInverseHistory Q M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω =
      ENNReal.ofReal (lemmaVInverseHistory Q bankField ((3 : ℝ) ^ (1 / 4 : ℝ))) := by
    rw [hroot]
    exact congrArg ENNReal.ofReal hhistory.symm
  have hfinite' : bankFiniteRootHistoryMax
      ({Q} : Finset (TriadicCube 2)) M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω ≠ ∞ := ne_of_lt hfinite
  have hmax := bank_member_history_le M ({Q} : Finset (TriadicCube 2)) Q
    (Finset.mem_singleton_self Q) m (m + 40)
    (bankPartialInsertionWeights m 1 t) ω
  have hInv0 : 0 ≤ lemmaVInverseHistory Q bankField ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
    rw [hhistory]
    exact mul_nonneg hσ.le (lemmaVInverseHistory_nonneg Q physicalCoeff hq)
  change lemmaVInverseHistory Q bankField ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ _
  change _ ≤ (bankFiniteRootHistoryMax ({Q} : Finset (TriadicCube 2))
    M m (m + 40) (bankPartialInsertionWeights m 1 t) ω).toReal
  calc
    lemmaVInverseHistory Q bankField ((3 : ℝ) ^ (1 / 4 : ℝ)) =
        (ENNReal.ofReal (lemmaVInverseHistory Q bankField ((3 : ℝ) ^ (1 / 4 : ℝ)))).toReal :=
      (ENNReal.toReal_ofReal hInv0).symm
    _ = (bankRootInverseHistory Q M m (m + 40)
        (bankPartialInsertionWeights m 1 t) ω).toReal := by rw [← hrootFrame]
    _ ≤ _ := ENNReal.toReal_mono hfinite' hmax

private theorem main_q3_source_inverse_history_le_bank_finite
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2)
    (hfinite : mainCutoffQ3SourceInverseBankMax M m t ω < ∞) :
    oldSignedInverseHistory (originCube 2 (m - 5))
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)) ≤
      (mainCutoffQ3SourceInverseBankMax M m t ω).toReal := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let P : TriadicCube 2 := originCube 2 m
  let σ : ℝ := Annealed.sigmaBar M m
  have hQdepth : Q ∈ descendantsAtDepth P 5 := by
    change originCube 2 (m - 5) ∈ descendantsAtDepth (originCube 2 m) 5
    exact originCube_mem_descendantsAtDepth' 2 m 5
  let insertionScale : ℤ := m + (1 : ℤ) - 1
  let f := modelInsertedScalar (closure (cubeSet P)) insertionScale t ω
  let localCoeff := mainInsertionSkewCoefficient m t Q ω
  let bankCoeff := pureFluxOpenResponseRestriction m f
  let localField := responseFramePlanarCoefficientField M.nu σ localCoeff
  let bankField := responseFramePlanarCoefficientField M.nu σ bankCoeff
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  have hcoef (x : Vec 2) (hx : x ∈ openCubeSet Q) :
      responseCoefficientExtension localCoeff x =
        responseCoefficientExtension bankCoeff x := by
    simpa only [Q, P, localCoeff, bankCoeff, f, insertionScale] using
      main_q3_source_response_coefficient_eq M m t ω x hx
  have hfields : localField =ᵐ[volumeMeasureOn (openCubeSet Q)] bankField := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    change responsePlanarCoefficient (M.nu / σ)
        (responseCoefficientExtension localCoeff x / σ) =
      responsePlanarCoefficient (M.nu / σ)
        (responseCoefficientExtension bankCoeff x / σ)
    rw [hcoef x hx]
  have hEllLocal : IsEllipticFieldOn (M.nu / σ) _ (openCubeSet Q) localField :=
    responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ localCoeff
  have hEllBankRoot : IsEllipticFieldOn (M.nu / σ) _ (openCubeSet P) bankField :=
    responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet P) M.nu σ M.nu_pos hσ bankCoeff
  have hEllBank : IsEllipticFieldOn (M.nu / σ) _ (openCubeSet Q) bankField :=
    hEllBankRoot.mono (measurableSet_openCubeSet Q)
      (openCubeSet_subset_of_mem_descendantsAtDepth hQdepth)
  have hcongr := old_signed_inverse_history_congr Q localField bankField
    hEllLocal hEllBank hfields
  have hbank := main_q3_source_bank_response_history_le_finite M m t ht ω hfinite
  change oldSignedInverseHistory Q localField ≤
    (mainCutoffQ3SourceInverseBankMax M m t ω).toReal
  change oldSignedInverseHistory Q bankField ≤
    (mainCutoffQ3SourceInverseBankMax M m t ω).toReal at hbank
  calc
    oldSignedInverseHistory Q localField = oldSignedInverseHistory Q bankField := hcongr
    _ ≤ (mainCutoffQ3SourceInverseBankMax M m t ω).toReal := hbank

/-- Actual OLD-frame inverse histories on the q3 source square have the
global-bank L2 cap `mainBeta`; the pointwise history comparison is included
so the same carrier can feed the oscillation profile row. -/
theorem main_q3_source_inverse_bank_and_history
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n < m, nativeInductionState M h n)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      mainCutoffQ3SourceInverseBankMax M m t ω < ∞) ∧
      MemLp (fun ω =>
        (mainCutoffQ3SourceInverseBankMax M m t ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (fun ω =>
        (mainCutoffQ3SourceInverseBankMax M m t ω).toReal) 2
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ mainBeta ∧
      ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        oldSignedInverseHistory (originCube 2 (m - 5))
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω)) ≤
          (mainCutoffQ3SourceInverseBankMax M m t ω).toReal := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  have hQscale : Q.scale = m - 5 := rfl
  have hweights : ∀ k ∈ Finset.Ioc m (m + 40),
      0 ≤ bankPartialInsertionWeights m 1 t k ∧
        bankPartialInsertionWeights m 1 t k ≤ 1 := by
    intro k hk
    exact bank_partial_insertion_weights_bounds m 1 t ht.2 k
  have hscale : ∀ R ∈ ({Q} : Finset (TriadicCube 2)),
      R.scale ≤ m ∧ m - R.scale ≤ 5 := by
    intro R hR
    have hRQ : R = Q := Finset.mem_singleton.mp hR
    subst R
    rw [hQscale]
    omega
  have hcard : ({Q} : Finset (TriadicCube 2)).card ≤ 6 * 9 ^ 45 := by
    simp
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hgamma m hpast).1
  have hBank : InverseBankConclusion M .globalInverse
      ({Q} : Finset (TriadicCube 2)) m (m + 40)
      (bankPartialInsertionWeights m 1 t) :=
    global_inverse_bank M h hM hgamma ({Q} : Finset (TriadicCube 2)) m (m + 40)
      (by omega) (bankPartialInsertionWeights m 1 t) hweights hscale hcard hpast hmean
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B := mainCutoffQ3SourceInverseBankMax M m t
  have hBeta : 0 ≤ mainBeta := by norm_num [mainBeta]
  have hcap : eLpNorm B 128 μ ≤ ENNReal.ofReal mainBeta := by
    change eLpNorm (bankFiniteRootHistoryMax ({Q} : Finset (TriadicCube 2))
      M m (m + 40) (bankPartialInsertionWeights m 1 t)) 128 μ ≤ _
    simpa only [mainBeta, inverseBankCap, Rat.cast_div, Rat.cast_ofNat] using
      hBank.total_L128
  have h128 := main_inverse_deficit_toReal_memLp_lp128_of_ennreal B
    mainBeta hBeta hBank.history_finite hcap
  have hmono : eLpNorm (fun ω => (B ω).toReal) 2 μ ≤
      eLpNorm (fun ω => (B ω).toReal) 128 μ :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2 : ℝ≥0∞) ≤ 128)
  have hcap128 : eLpNorm (fun ω => (B ω).toReal) 128 μ ≤ ENNReal.ofReal mainBeta := by
    rw [← ENNReal.ofReal_toReal h128.1.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal (by simpa only [lpNorm] using h128.2)
  have hB2 : MemLp (fun ω => (B ω).toReal) 2 μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt (hmono.trans hcap128) ENNReal.ofReal_lt_top
  have hnorm : lpNorm (fun ω => (B ω).toReal) 2 μ ≤ mainBeta := by
    change (eLpNorm (fun ω => (B ω).toReal) 2 μ).toReal ≤ mainBeta
    calc
      _ ≤ (eLpNorm (fun ω => (B ω).toReal) 128 μ).toReal :=
        ENNReal.toReal_mono h128.1.eLpNorm_ne_top hmono
      _ ≤ (ENNReal.ofReal mainBeta).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hcap128
      _ = mainBeta := ENNReal.toReal_ofReal hBeta
  refine ⟨hBank.history_finite, hB2, hnorm, ?_⟩
  filter_upwards [hBank.history_finite] with ω hfinite
  exact main_q3_source_inverse_history_le_bank_finite M m t ht ω hfinite

end
end ASDExplicitGamma.Main
