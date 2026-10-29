module

public import ASDExplicitGamma.Gaussian.BasisIndependence
public import ASDExplicitGamma.Inverse.BankOnePassHeat
public import ASDExplicitGamma.Inverse.BankOnePassLocal
public import ASDExplicitGamma.Inverse.ResponseCoefficients
public import ASDExplicitGamma.Inverse.PureFluxGeneratorOpenBridge
public import ASDExplicitGamma.Inverse.PureFluxGeneratorActualQ3
public import ASDExplicitGamma.Main.CubeFactor
public import ASDExplicitGamma.Scalar.InverseHistoryBlocks
public import ASDExplicitGamma.Variational.LemmaVH1
public import ASDExplicitGamma.Variational.AdapterShearTrace

/-! The arbitrary Gaussian coordinates in the bank input can be replaced by
the actual q3 H3 realization of the fresh shell. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Model ASDExplicitGamma.Scalar
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal

namespace ASDExplicitGamma.Inverse

local instance pureFluxBankLawCompact (P : TriadicCube 2) :
    CompactSpace (closure (cubeSet P)) :=
  isCompact_iff_compactSpace.mp (isBounded_cubeSet P).isCompact_closure

private noncomputable def pureFluxClosedCubeInclusion {P R : TriadicCube 2}
    {d : ℕ} (hR : R ∈ descendantsAtDepth P d) :
    C(closure (cubeSet R), closure (cubeSet P)) :=
  ⟨fun x => ⟨x.1, closure_mono (cubeSet_subset_of_mem_descendantsAtDepth hR) x.2⟩,
    continuous_subtype_val.subtype_mk _⟩

private noncomputable def pureFluxResponseCoefficientOnDescendant
    {P R : TriadicCube 2} {d : ℕ} (hR : R ∈ descendantsAtDepth P d) :
    C(closure (cubeSet P), ℝ) →L[ℝ] ResponseCoefficient (cubeSet R) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    (pureFluxClosedCubeInclusion hR)).comp
    (ContinuousMap.linearIsometryBoundedOfCompact
      (closure (cubeSet P)) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap

private theorem pureFluxResponseCoefficientOnDescendant_extension
    {P R : TriadicCube 2} {d : ℕ}
    (hR : R ∈ descendantsAtDepth P d)
    (f : C(closure (cubeSet P), ℝ)) {x : Vec 2} (hx : x ∈ cubeSet R) :
    responseCoefficientExtension (pureFluxResponseCoefficientOnDescendant hR f) x =
      f ⟨x, subset_closure ((cubeSet_subset_of_mem_descendantsAtDepth hR) hx)⟩ := by
  rw [responseCoefficientExtension_eq _ hx]
  simp [pureFluxResponseCoefficientOnDescendant,
    pureFluxClosedCubeInclusion,
    BoundedContinuousFunction.compContinuousCLM_apply,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]

private theorem pureFlux_symmPart_partialInsertedCoefficient
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    Homogenization.symmPart (Model.partialInsertedCoefficient M m t ω x) =
      M.nu • (1 : Mat 2) := by
  have hsum (A B : Mat 2) : Homogenization.symmPart (A + B) =
      Homogenization.symmPart A + Homogenization.symmPart B := by
    ext i j
    simp only [Homogenization.symmPart, Matrix.add_apply]
    ring
  have hsmul (c : ℝ) (A : Mat 2) : Homogenization.symmPart (c • A) =
      c • Homogenization.symmPart A := by
    ext i j
    simp only [Homogenization.symmPart, Matrix.smul_apply]
    ring
  have hskew : Homogenization.symmPart (ShellField.forgetShell (ω.1 (m + 1)) x) = 0 := by
    ext i j
    change ((ω.1 (m + 1)) x i j + (ω.1 (m + 1)) x j i) / 2 = 0
    rw [(ω.1 (m + 1)).skew_entry x i j]
    ring
  change Homogenization.symmPart
    (Cutoff.coefficientCutoff M.nu m ω x +
      Real.sqrt t • ShellField.forgetShell (ω.1 (m + 1)) x) = _
  rw [hsum, hsmul, hskew, smul_zero, add_zero,
    Cutoff.symmPart_coefficientCutoff]

/-- On every closed triadic descendant of the insertion cube, the open-cube
response frame has the same coarse matrix as the physical partial insertion
put into the deterministic σ-frame. -/
theorem pureFlux_partialInsertion_coarseMatrix_frame
    (k : ℤ) (M : ABKModel 2) (ell : ℤ)
    (hK : closure (cubeSet (originCube 2 k)) ⊆ openCubeSet (originCube 2 ell))
    (s : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2)
    {R : TriadicCube 2} {d : ℕ}
    (hR : R ∈ descendantsAtDepth (originCube 2 k) d) :
    coarseBlockMatrix (cubeSet R)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M k : ℝ)
        (pureFluxOpenResponseRestriction k
          (modelInsertedScalar (closure (cubeSet (originCube 2 k)))
            (k + (s : ℤ) - 1) t ω))) =
    frameMatrix (Annealed.sigmaBar M k : ℝ)
      (coarseBlockMatrix (cubeSet R)
        (Model.partialInsertedCoefficient M (k + (s : ℤ) - 1) t ω).toFun) := by
  let P := originCube 2 k
  let K := closure (cubeSet P)
  let f := modelInsertedScalar K (k + (s : ℤ) - 1) t ω
  let hRcoeff := pureFluxResponseCoefficientOnDescendant hR f
  let σ := (Annealed.sigmaBar M k : ℝ)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M k).1
  have hsource (x : Vec 2) (hx : x ∈ openCubeSet R) :
      responseFramePlanarCoefficientField M.nu σ (pureFluxOpenResponseRestriction k f) x =
        responseFramePlanarCoefficientField M.nu σ hRcoeff x := by
    change responsePlanarCoefficient (M.nu / σ)
        (responseCoefficientExtension (pureFluxOpenResponseRestriction k f) x / σ) =
      responsePlanarCoefficient (M.nu / σ)
        (responseCoefficientExtension hRcoeff x / σ)
    have hxP := openCubeSet_subset_of_mem_descendantsAtDepth hR hx
    rw [pureFluxOpenResponseRestriction_value k f hxP,
      pureFluxResponseCoefficientOnDescendant_extension hR f
        (openCubeSet_subset_cubeSet R hx)]
  have hframe :
      coarseBlockMatrix (cubeSet R)
        (responseFramePlanarCoefficientField M.nu σ (pureFluxOpenResponseRestriction k f)) =
      coarseBlockMatrix (cubeSet R)
        (responseFramePlanarCoefficientField M.nu σ hRcoeff) := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact hsource x hx
  have hphysical (x : Vec 2) (hx : x ∈ openCubeSet R) :
      responsePlanarCoefficientField M.nu hRcoeff x =
        (Model.partialInsertedCoefficient M (k + (s : ℤ) - 1) t ω).toFun x := by
    change responsePlanarCoefficient M.nu (responseCoefficientExtension hRcoeff x) = _
    rw [pureFluxResponseCoefficientOnDescendant_extension hR f
      (openCubeSet_subset_cubeSet R hx)]
    have hxP : x ∈ openCubeSet P :=
      openCubeSet_subset_of_mem_descendantsAtDepth hR hx
    let xK : K := ⟨x, subset_closure (openCubeSet_subset_cubeSet P hxP)⟩
    have hscalar := modelInsertedScalar_apply K M ell (k + (s : ℤ) - 1)
      hK t ω xK
    have hscalar' : f ⟨x, subset_closure
        ((cubeSet_subset_of_mem_descendantsAtDepth hR)
          (openCubeSet_subset_cubeSet R hx))⟩ =
        (Model.partialInsertedCoefficient M (k + (s : ℤ) - 1) t ω).toFun x 1 0 := by
      simpa [f, xK] using hscalar
    have hmatrix := pureFlux_symmPart_partialInsertedCoefficient M
      (k + (s : ℤ) - 1) t ω x
    rw [hscalar']
    exact planar_coefficient_eq_of_symmPart M.nu _ hmatrix
  have hphysicalMatrix :
      coarseBlockMatrix (cubeSet R)
        (responsePlanarCoefficientField M.nu hRcoeff) =
      coarseBlockMatrix (cubeSet R)
        (Model.partialInsertedCoefficient M (k + (s : ℤ) - 1) t ω).toFun := by
    rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
      coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R]
    apply coarseBlockMatrix_congr_of_ae_eq
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    exact hphysical x hx
  calc
    coarseBlockMatrix (cubeSet R)
        (responseFramePlanarCoefficientField M.nu σ (pureFluxOpenResponseRestriction k f)) =
        coarseBlockMatrix (cubeSet R)
          (responseFramePlanarCoefficientField M.nu σ hRcoeff) := hframe
    _ = frameMatrix σ (coarseBlockMatrix (cubeSet R)
          (responsePlanarCoefficientField M.nu hRcoeff)) := by
        exact response_coarseMatrix_frame_eq (measurableSet_cubeSet R)
          M.nu σ M.nu_pos hσ hRcoeff
    _ = frameMatrix σ (coarseBlockMatrix (cubeSet R)
          (Model.partialInsertedCoefficient M (k + (s : ℤ) - 1) t ω).toFun) := by
        rw [hphysicalMatrix]

/-- Every source-mesh tile has its actual framed inverse history bounded by
the same one-pass local bank history. The finite-history event is the only
probabilistic premise; all coefficient and frame identifications are derived
from the partial insertion itself. -/
private theorem pureFlux_inverseHistory_frame_eq_aux
    (Q : TriadicCube 2) (a af : CoeffField 2)
    {lam Lam laf Laf σ q : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hEllFrame : IsEllipticFieldOn laf Laf (openCubeSet Q) af)
    (hσ : 0 < σ)
    (hMatrix : ∀ (R : TriadicCube 2) (d : ℕ)
      (_hR : R ∈ descendantsAtDepth Q d),
      coarseBlockMatrix (cubeSet R) af =
        frameMatrix σ (coarseBlockMatrix (cubeSet R) a)) :
    lemmaVInverseHistory Q af q = σ * lemmaVInverseHistory Q a q := by
  have hdepth (d : ℕ) : lemmaVInverseDepthMax Q af d =
      σ * lemmaVInverseDepthMax Q a d := by
    rw [lemmaVInverseDepthMax,
      ← inverse_history_framed_depth_max Q a hEll σ hσ d]
    apply Book.Ch02.finsetSupReal_congr
    intro R hR
    rw [inverse_history_lowerRight R af
      (hEllFrame.mono (measurableSet_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR)), hMatrix R d hR]
    simp [frameMatrix]
  unfold lemmaVInverseHistory
  simp_rw [hdepth]
  calc
    (1 - q⁻¹) * ∑' d : ℕ, (q⁻¹)^d *
        (σ * lemmaVInverseDepthMax Q a d) =
      (1 - q⁻¹) * (σ * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by
        congr 1
        calc
          ∑' d : ℕ, (q⁻¹)^d * (σ * lemmaVInverseDepthMax Q a d) =
              ∑' d : ℕ, σ * ((q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by
                apply tsum_congr
                intro d
                ring
          _ = σ * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d := tsum_mul_left
    _ = σ * ((1 - q⁻¹) * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by ring

private theorem pureFlux_descendant_in_local_roots
    (P U : TriadicCube 2) (m : ℕ) (hm : m ≤ 5)
    (hU : U ∈ descendantsAtDepth P m) : U ∈ bankLocalRoots P 5 := by
  rw [bankLocalRoots, Finset.mem_insert]
  right
  rw [Finset.mem_biUnion]
  exact ⟨m, Finset.mem_range.mpr (by omega), hU⟩

theorem pureFlux_bank_source_mesh_history_le
    (M : ABKModel 2) (k : ℤ) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) (m : ℕ) (hm : m ≤ 5)
    (hfinite : bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 k) 5)
      M k (k + 40) (bankPartialInsertionWeights k s t) ω ≠ ∞)
    {U : TriadicCube 2} (hU : U ∈ descendantsAtDepth (originCube 2 k) m) :
    lemmaVInverseHistory U
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M k : ℝ)
          (pureFluxOpenResponseRestriction k
            (modelInsertedScalar (closure (cubeSet (originCube 2 k)))
              (k + (s : ℤ) - 1) t ω)))
        ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
      (bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 k) 5)
        M k (k + 40) (bankPartialInsertionWeights k s t) ω).toReal := by
  let P := originCube 2 k
  let K := closure (cubeSet P)
  let f := modelInsertedScalar K (k + (s : ℤ) - 1) t ω
  let H := pureFluxOpenResponseRestriction k f
  let σ := (Annealed.sigmaBar M k : ℝ)
  let a := attenuatedCoefficient M k (k + 40)
    (bankPartialInsertionWeights k s t) ω
  let af := responseFramePlanarCoefficientField M.nu σ H
  let q := (3 : ℝ) ^ (1 / 4 : ℝ)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M k).1
  have hq : 1 < q := Real.one_lt_rpow (by norm_num) (by norm_num)
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet P).isCompact_closure
  let Lam : ℝ := ((2 : ℝ) * 2 * (Model.partialInsertedEntryBound M ell
    (k + (s : ℤ) - 1) ω) ^ 2 + M.nu ^ 2) / M.nu
  have hEllPartial : IsEllipticFieldOn M.nu Lam (openCubeSet P)
      (Model.partialInsertedCoefficient M (k + (s : ℤ) - 1) t ω).toFun := by
    simpa [Lam] using
      (Model.partialInsertedCoefficient_isEllipticFieldOn M ell
        (k + (s : ℤ) - 1) ω ⟨ht.1, ht.2⟩
        (measurableSet_openCubeSet P)
        (fun _ hx => hK (subset_closure (openCubeSet_subset_cubeSet P hx))))
  have hcoeff := bank_one_pass_partial_coefficient M k s hs t ω
  have hEll : IsEllipticFieldOn M.nu Lam (openCubeSet P) a := by
    simpa only [a, ← hcoeff] using hEllPartial
  have hEllFrame := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet P) M.nu σ M.nu_pos hσ H
  have hMatrix (V : TriadicCube 2) (j : ℕ)
      (hV : V ∈ descendantsAtDepth U j) :
      coarseBlockMatrix (cubeSet V) af =
        frameMatrix σ (coarseBlockMatrix (cubeSet V) a) := by
    have hVP : V ∈ descendantsAtDepth P (m + j) := by
      simpa [Nat.add_comm] using mem_descendantsAtDepth_add hU hV
    have hpartial := pureFlux_partialInsertion_coarseMatrix_frame
      k M ell hK s t ω hVP
    simpa only [af, σ, a, hcoeff] using hpartial
  have hEllU := hEll.mono (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hEllFrameU := hEllFrame.mono (measurableSet_openCubeSet U)
    (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hFrameHistory : lemmaVInverseHistory U af q = σ * lemmaVInverseHistory U a q :=
    pureFlux_inverseHistory_frame_eq_aux U a af hEllU hEllFrameU hσ (q := q)
      (fun V j hV => hMatrix V j hV)
  have hRootHistory := bank_root_history_physical U M k (k + 40)
    (bankPartialInsertionWeights k s t) ω a rfl hEllU
  have hHistoryEq : lemmaVInverseHistory U af q =
      (bankRootInverseHistory U M k (k + 40)
        (bankPartialInsertionWeights k s t) ω).toReal := by
    rw [hFrameHistory, hRootHistory, ENNReal.toReal_ofReal]
    exact mul_nonneg hσ.le (lemmaVInverseHistory_nonneg U a hq)
  have hRoot : U ∈ bankLocalRoots P 5 :=
    pureFlux_descendant_in_local_roots P U m hm hU
  have hmax := bank_member_history_le M (bankLocalRoots P 5) U hRoot
    k (k + 40) (bankPartialInsertionWeights k s t) ω
  have hmaxReal := ENNReal.toReal_mono hfinite hmax
  change lemmaVInverseHistory U af q ≤ _
  calc
    lemmaVInverseHistory U af q =
        (bankRootInverseHistory U M k (k + 40)
          (bankPartialInsertionWeights k s t) ω).toReal := hHistoryEq
    _ ≤ (bankFiniteRootHistoryMax (bankLocalRoots P 5) M k (k + 40)
          (bankPartialInsertionWeights k s t) ω).toReal := hmaxReal

/-- The covariance trace in the bank's arbitrary fresh-shell realization is
the same as the trace in the canonical q3 H3 realization. The law premise is
exactly the one in `BankPureFluxGeneratorInput`; no covariance bound is
assumed here. -/
theorem pureFlux_bank_covarianceTrace_eq_actual_q3
    (k : ℤ) (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (s : ℕ) (_t : ℝ)
    (T : GaussianFactorL2 ℕ →L[ℝ]
      C(closure (cubeSet (originCube 2 k)), ℝ))
    (v : ℕ → GaussianFactorL2 ℕ)
    (hA : Summable (fun j => ‖v j‖ ^ 2))
    (hlaw : (Cutoff.cutoffSampleLaw M).toMeasure.map
      (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction
        (closure (cubeSet (originCube 2 k))) (ω.1 (k + (s : ℤ)))) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T))
    (x : C(closure (cubeSet (originCube 2 k)), ℝ)) :
    modelCovarianceTrace
        (bankInverseTraceObservable k M.nu (Annealed.sigmaBar M k : ℝ)
          M.nu_pos (Annealed.sigmaBar_characterization M k).1)
        (fun j => T (v j)) x =
      modelCovarianceTrace
        (bankInverseTraceObservable k M.nu (Annealed.sigmaBar M k : ℝ)
          M.nu_pos (Annealed.sigmaBar_characterization M k).1)
        (pureFluxMainCubeQ3Directions k (q3ModelAmplitude M h (k + (s : ℤ)))
          (q3ModelLength (k + (s : ℤ)))) x := by
  let b := q3ModelAmplitude M h (k + (s : ℤ))
  let L := q3ModelLength (k + (s : ℤ))
  have hactual := main_actual_fresh_cube_factor_law k M h hM (k + (s : ℤ) - 1)
  have hcanonical :
      standardGaussianInfinitePi.map (mainCubeQ3Series k b L) =
      standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) := by
    have hactual' : (Cutoff.cutoffSampleLaw M).toMeasure.map
        (fun ω : Cutoff.CutoffSample 2 => shellFieldScalarRestriction
          (closure (cubeSet (originCube 2 k))) (ω.1 (k + (s : ℤ)))) =
        standardGaussianInfinitePi.map (mainCubeQ3Series k b L) := by
      simpa [b, L] using hactual
    exact hactual'.symm.trans hlaw
  have hΦ : HasPolynomiallyBoundedC2Derivatives
      (bankInverseTraceObservable k M.nu (Annealed.sigmaBar M k : ℝ)
        M.nu_pos (Annealed.sigmaBar_characterization M k).1) :=
    bank_inverse_trace_observable_C2 k M.nu (Annealed.sigmaBar M k : ℝ)
      M.nu_pos (Annealed.sigmaBar_characterization M k).1
  have htrace := @modelCovarianceTrace_eq_of_law
    (GaussianFactorL2 ℕ) (MainCubeH3 k b L)
    (C(closure (cubeSet (originCube 2 k)), ℝ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance (mainCubeH3InnerProductSpace k b L) inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance
    v hA T (mainCubeQ3Directions k b L) (mainCubeQ3Directions_summable k b L)
    (mainCubeH3Value k b L) hcanonical.symm
    (bankInverseTraceObservable k M.nu (Annealed.sigmaBar M k : ℝ)
      M.nu_pos (Annealed.sigmaBar_characterization M k).1) hΦ x
  change modelCovarianceTrace _ (fun j => T (v j)) x =
    modelCovarianceTrace _ (fun j => mainCubeH3Value k
      (q3ModelAmplitude M h (k + (s : ℤ)))
      (q3ModelLength (k + (s : ℤ)))
      (mainCubeQ3Directions k (q3ModelAmplitude M h (k + (s : ℤ)))
        (q3ModelLength (k + (s : ℤ))) j)) x
  exact htrace

/-- The bank inverse-trace observable is invariant under a constant skew
shift of the physical scalar coefficient. This is the gauge identity needed
to center each fresh Gaussian direction at the parent cube center. -/
theorem bank_inverse_trace_observable_add_const
    (q : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (f : C(closure (cubeSet (originCube 2 q)), ℝ)) (g : ℝ) :
    bankInverseTraceObservable q ν σ hν hσ
        (f + ContinuousMap.const (closure (cubeSet (originCube 2 q))) g) =
      bankInverseTraceObservable q ν σ hν hσ f := by
  let Q := originCube 2 q
  let U := cubeSet Q
  let K := closure U
  let L := ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ
  let k := L f
  have hL : L (f + ContinuousMap.const K g) = k + BoundedContinuousFunction.const K g := by
    ext x
    simp [L, k]
  have hcoeff (x : Vec 2) (hx : x ∈ U) :
      responseCoefficientExtension (L (f + ContinuousMap.const K g)) x =
        responseCoefficientExtension k x + g := by
    rw [hL]
    rw [responseCoefficientExtension_add_on k (BoundedContinuousFunction.const K g) hx]
    rw [responseCoefficientExtension_eq (BoundedContinuousFunction.const K g) hx]
    rfl
  have hfield : responsePlanarCoefficientField ν (L (f + ContinuousMap.const K g)) =ᵐ[
      volume.restrict U]
      (fun x => responsePlanarCoefficient ν (responseCoefficientExtension k x + g)) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_cubeSet Q)] with x hx
    simp only [responsePlanarCoefficientField, hcoeff x hx]
  have hmatrix :
      coarseBlockMatrix U (responsePlanarCoefficientField ν (L (f + ContinuousMap.const K g))) =
        constantSkewCongruence g
          (coarseBlockMatrix U (responsePlanarCoefficientField ν k)) := by
    rw [coarseBlockMatrix_congr_of_ae_eq hfield]
    exact response_coarseBlockMatrix_constantSkew Q ν hν k g
  rw [bank_inverse_trace_observable_eq q ν σ hν hσ
      (f + ContinuousMap.const K g),
    bank_inverse_trace_observable_eq q ν σ hν hσ f]
  unfold bankInverseTrace
  rw [hmatrix]
  simp only [constantSkewCongruence_lowerRight]
  rfl

/-- A fixed-frame coarse-matrix identity transfers every inverse depth maximum
to the physical frame. The two ellipticity hypotheses are only used to identify
the source inverse with the actual lower-right coarse block on each tile. -/
theorem pureFlux_inverseDepthMax_frame_eq
    (Q : TriadicCube 2) (a af : CoeffField 2)
    {lam Lam laf Laf σ : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hEllFrame : IsEllipticFieldOn laf Laf (openCubeSet Q) af)
    (hσ : 0 < σ)
    (d : ℕ)
    (hMatrixD : ∀ (R : TriadicCube 2) (_hR : R ∈ descendantsAtDepth Q d),
      coarseBlockMatrix (cubeSet R) af =
        frameMatrix σ (coarseBlockMatrix (cubeSet R) a)) :
    lemmaVInverseDepthMax Q af d = σ * lemmaVInverseDepthMax Q a d := by
  rw [lemmaVInverseDepthMax,
    ← inverse_history_framed_depth_max Q a hEll σ hσ d]
  apply Book.Ch02.finsetSupReal_congr
  intro R hR
  rw [inverse_history_lowerRight R af
    (hEllFrame.mono (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)), hMatrixD R hR]
  simp [frameMatrix]

/-- The complete Lemma-V inverse history has the same fixed-frame scaling as
every finite inverse depth maximum. -/
theorem pureFlux_inverseHistory_frame_eq
    (Q : TriadicCube 2) (a af : CoeffField 2)
    {lam Lam laf Laf σ q : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hEllFrame : IsEllipticFieldOn laf Laf (openCubeSet Q) af)
    (hσ : 0 < σ)
    (hMatrix : ∀ (R : TriadicCube 2) (d : ℕ)
      (_hR : R ∈ descendantsAtDepth Q d),
      coarseBlockMatrix (cubeSet R) af =
        frameMatrix σ (coarseBlockMatrix (cubeSet R) a)) :
    lemmaVInverseHistory Q af q = σ * lemmaVInverseHistory Q a q := by
  have hdepth (d : ℕ) : lemmaVInverseDepthMax Q af d =
      σ * lemmaVInverseDepthMax Q a d :=
    pureFlux_inverseDepthMax_frame_eq Q a af hEll hEllFrame hσ d
      (hMatrix · d)
  unfold lemmaVInverseHistory
  simp_rw [hdepth]
  calc
    (1 - q⁻¹) * ∑' d : ℕ, (q⁻¹)^d *
        (σ * lemmaVInverseDepthMax Q a d) =
      (1 - q⁻¹) * (σ * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by
        congr 1
        calc
          ∑' d : ℕ, (q⁻¹)^d * (σ * lemmaVInverseDepthMax Q a d) =
              ∑' d : ℕ, σ * ((q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by
                apply tsum_congr
                intro d
                ring
          _ = σ * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d := tsum_mul_left
    _ = σ * ((1 - q⁻¹) * ∑' d : ℕ, (q⁻¹)^d * lemmaVInverseDepthMax Q a d) := by ring

end ASDExplicitGamma.Inverse
