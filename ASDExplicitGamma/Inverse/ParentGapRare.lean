module

public import ASDExplicitGamma.Inverse.BridgeObservables
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Main.AffineMatrixMoments
public import ASDExplicitGamma.Native.OldSignedAffineIdentification
public import ASDExplicitGamma.Scalar.CutoffMeasurability
public import ASDExplicitGamma.Scalar.FlatSourceQ3PositiveHaar
public import ASDExplicitGamma.Triadic.DiagEnergyCongr
public import Algsuperdiff.Section3.Provider.BadEvents.LiteralMeasurabilityEngine
public import Homogenization.Book.Ch04.Theorems.WidetildeTheta

/-! Actual cutoff-law measurability for the global inverse maximum and the
paired OLD-frame weak-error observables used by the parent-gap assembly. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Native
open ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
open scoped BigOperators ENNReal

noncomputable local instance parent_gap_blockL2_measurableSpace
    (Q : TriadicCube 2) : MeasurableSpace (BlockL2 (openCubeSet Q)) := borel _

local instance parent_gap_blockL2_borelSpace
    (Q : TriadicCube 2) : BorelSpace (BlockL2 (openCubeSet Q)) := ⟨rfl⟩

local instance parent_gap_blockL2_opensMeasurableSpace
    (Q : TriadicCube 2) : OpensMeasurableSpace (BlockL2 (openCubeSet Q)) :=
  ⟨le_of_eq rfl⟩

local instance parent_gap_hilbertBlockL2_opensMeasurableSpace
    (Q : TriadicCube 2) : OpensMeasurableSpace (HilbertBlockL2 (openCubeSet Q)) :=
  ⟨le_of_eq rfl⟩

private theorem parent_gap_symmPart_partialInserted
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (x : Vec 2) :
    Homogenization.symmPart (Model.partialInsertedCoefficient M m t ω x) =
      M.nu • (1 : Mat 2) := by
  have hbase := Cutoff.symmPart_coefficientCutoff M.nu m ω x
  ext i j
  have hb := congrFun (congrFun hbase i) j
  have hskew := (ω.1 (m + 1)).skew_entry x i j
  change (Cutoff.coefficientCutoff M.nu m ω x i j +
      Cutoff.coefficientCutoff M.nu m ω x j i) / 2 =
    (M.nu • (1 : Mat 2)) i j at hb
  change (Cutoff.coefficientCutoff M.nu m ω x i j +
      Real.sqrt t * ω.1 (m + 1) x i j +
      (Cutoff.coefficientCutoff M.nu m ω x j i +
        Real.sqrt t * ω.1 (m + 1) x j i)) / 2 = _
  rw [hskew]
  linarith

private theorem parent_gap_partialInserted_isEllipticOn_cube
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (Q : TriadicCube 2) :
    ∃ Λ : ℝ, IsEllipticFieldOn M.nu Λ (cubeSet Q)
      (Model.partialInsertedCoefficient M m t ω).toFun ∧ M.nu ≤ Λ := by
  classical
  let K := closure (cubeSet Q)
  have hK : IsCompact K := (isBounded_cubeSet Q).isCompact_closure
  obtain ⟨N, hcover⟩ := Cutoff.exists_nat_openOriginCube_of_isCompact hK
  have hcover' : ∀ x ∈ cubeSet Q,
      x ∈ openCubeSet (originCube 2 (N : ℤ)) :=
    fun x hx => hcover (subset_closure hx)
  let C : ℝ := M.nu + Cutoff.cutoffLocalControl (N : ℤ) m ω +
    Real.sqrt t * localCubeControl (N : ℤ) (ω.1 (m + 1))
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (add_nonneg M.nu_pos.le
      (Cutoff.cutoffLocalControl_nonneg (N : ℤ) m ω))
      (mul_nonneg (Real.sqrt_nonneg _) (localCubeControl_nonneg (N : ℤ) _))
  have hEll : IsEllipticFieldOn M.nu
    (((2 : ℝ) * 2 * C ^ 2 + M.nu ^ 2) / M.nu)
    (cubeSet Q) (Model.partialInsertedCoefficient M m t ω).toFun
  · refine ⟨?_, ?_⟩
    · apply measurable_pi_iff.mpr
      intro i
      apply measurable_pi_iff.mpr
      intro j
      exact ((Model.partialInsertedCoefficient M m t ω).entry_measurable i j).ite
        (measurableSet_cubeSet Q) measurable_const
    · intro x hx
      apply Cutoff.isEllipticMatrix_of_symmPart_and_entry_bound M.nu_pos
        (parent_gap_symmPart_partialInserted M m t ω x)
      intro i j
      have hbase := Cutoff.abs_coefficientCutoff_entry_le M.nu M.nu_pos.le
        (N : ℤ) m ω (hcover' x hx) i j
      have hfresh := abs_entry_le_localCubeControl (N : ℤ) (ω.1 (m + 1))
        (hcover' x hx) i j
      have hscaled : Real.sqrt t * |ω.1 (m + 1) x i j| ≤
          Real.sqrt t * localCubeControl (N : ℤ) (ω.1 (m + 1)) :=
        mul_le_mul_of_nonneg_left (by simpa using hfresh) (Real.sqrt_nonneg _)
      change |Cutoff.coefficientCutoff M.nu m ω x i j +
          Real.sqrt t * ω.1 (m + 1) x i j| ≤ C
      calc
        _ ≤ |Cutoff.coefficientCutoff M.nu m ω x i j| +
            |Real.sqrt t * ω.1 (m + 1) x i j| := abs_add_le _ _
        _ = |Cutoff.coefficientCutoff M.nu m ω x i j| +
            Real.sqrt t * |ω.1 (m + 1) x i j| := by
          rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        _ ≤ M.nu + Cutoff.cutoffLocalControl (N : ℤ) m ω +
            Real.sqrt t * localCubeControl (N : ℤ) (ω.1 (m + 1)) :=
          add_le_add hbase hscaled
        _ = C := rfl
  have hΛ : M.nu ≤ ((2 : ℝ) * 2 * C ^ 2 + M.nu ^ 2) / M.nu := by
    apply (le_div_iff₀ M.nu_pos).2
    nlinarith [sq_nonneg C]
  exact ⟨_, hEll, hΛ⟩

private theorem parent_gap_partialInserted_locallyElliptic
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    Book.Ch04.AELocallyUniformlyEllipticField
      (Model.partialInsertedCoefficient M m t ω) := by
  intro Q
  obtain ⟨Λ, hEll, hΛ⟩ := parent_gap_partialInserted_isEllipticOn_cube M m t ω Q
  have hOpen := hEll.mono (measurableSet_openCubeSet Q) (openCubeSet_subset_cubeSet Q)
  obtain ⟨x, hx⟩ := Book.Ch02.openCubeSet_nonempty Q
  exact ⟨M.nu, Λ, M.nu_pos, hΛ,
    IsAEEllipticFieldOn.of_isEllipticFieldOn hOpen⟩

private theorem parent_gap_root_depth_max_measurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2) (d : ℕ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      lemmaVInverseDepthMax Q (Model.partialInsertedCoefficient M m t ω).toFun d) := by
  classical
  let X := Model.partialInsertedCoefficient M m t
  have hX : Measurable X := Main.mainInsertion_partialInsertedCoefficient_measurable M m t
  have hEll : ∀ ω, Book.Ch04.AELocallyUniformlyEllipticField (X ω) :=
    fun ω => parent_gap_partialInserted_locallyElliptic M m t ω
  have hLR R : Measurable (fun ω =>
      (coarseBlockMatrix (cubeSet R) (X ω).toFun).lowerRight) :=
    Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet hX hEll R
  let L : Mat 2 →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
    { toFun := fun A => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A
      map_add' := fun A B => map_add (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) A B
      map_smul' := fun c A => map_smul (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) c A }
  have hL : Continuous L := L.continuous_of_finiteDimensional
  have hnorm : ∀ R, Measurable (fun ω =>
      Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) (X ω).toFun)) := by
    intro R
    have hn : Measurable (fun ω =>
        ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
          ((coarseBlockMatrix (cubeSet R) (X ω).toFun).lowerRight)‖) :=
      hL.norm.measurable.comp (hLR R)
    have heq (ω : Cutoff.CutoffSample 2) :
        sigmaStarInvCoarse (openCubeSet R) (X ω).toFun =
          (coarseBlockMatrix (cubeSet R) (X ω).toFun).lowerRight := by
      obtain ⟨Λ, hEll, hΛ⟩ := parent_gap_partialInserted_isEllipticOn_cube
        M m t ω R
      exact Scalar.inverse_history_lowerRight R (X ω).toFun
        (hEll.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R))
    have hfun : (fun ω => Book.Ch02.matrixNorm
        (sigmaStarInvCoarse (openCubeSet R) (X ω).toFun)) =
        fun ω => ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)
          ((coarseBlockMatrix (cubeSet R) (X ω).toFun).lowerRight)‖ := by
      funext ω
      rw [heq ω]
      rfl
    rw [hfun]
    exact hn
  let S := descendantsAtDepth Q d
  have hS : S.Nonempty := descendantsAtDepth_nonempty Q d
  have hsup : Measurable (S.sup' hS fun R ω =>
      Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) (X ω).toFun)) :=
    Finset.measurable_sup' hS (fun R hR => hnorm R)
  have heq : (fun ω : Cutoff.CutoffSample 2 =>
      lemmaVInverseDepthMax Q (X ω).toFun d) =
      S.sup' hS (fun R ω =>
        Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) (X ω).toFun)) := by
    funext ω
    change Book.Ch02.finsetSupReal S _ = _
    rw [Homogenization.Book.Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' S hS]
    simp only [Finset.sup'_apply]
  rw [heq]
  exact hsup

private theorem parent_gap_root_history_measurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (Q : TriadicCube 2) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      lemmaVInverseHistory Q (Model.partialInsertedCoefficient M m t ω).toFun
        ((3 : ℝ) ^ (1 / 4 : ℝ))) := by
  let r : ℝ := ((3 : ℝ) ^ (1 / 4 : ℝ))⁻¹
  have hterm d : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      r ^ d * lemmaVInverseDepthMax Q
        (Model.partialInsertedCoefficient M m t ω).toFun d) :=
    measurable_const.mul (parent_gap_root_depth_max_measurable M m t Q d)
  change Measurable (fun ω => (1 - r) * ∑' d : ℕ,
    r ^ d * lemmaVInverseDepthMax Q
      (Model.partialInsertedCoefficient M m t ω).toFun d)
  exact measurable_const.mul (Measurable.tsum hterm)

/-- The actual finite global inverse maximum is measurable under the cutoff
law. The proof treats the full coefficient for arbitrary real insertion time. -/
theorem parent_gap_bstar_measurable (M : ABKModel 2) (m : ℤ) (t : ℝ) :
    Measurable (mixedBridgeBstar M m t) := by
  classical
  let S := mixedBridgeObserverSourceRoots m
  have hS : S.Nonempty := by
    change ((Finset.range 6).biUnion fun r =>
      descendantsAtDepth (originCube 2 (m + 40)) (40 + r)).Nonempty
    apply Finset.Nonempty.biUnion
    · exact ⟨0, by simp⟩
    · intro r hr
      exact descendantsAtDepth_nonempty _ _
  have hroot (Q : TriadicCube 2) :
      Measurable (fun ω : Cutoff.CutoffSample 2 =>
        mixedBridgeRootHistoryProfile M m t ω Q) := by
    change Measurable (fun ω => (Annealed.sigmaBar M m : ℝ) *
      lemmaVInverseHistory Q
        (Model.partialInsertedCoefficient M m t ω).toFun ((3 : ℝ) ^ (1 / 4 : ℝ)))
    exact measurable_const.mul (parent_gap_root_history_measurable M m t Q)
  have hsup : Measurable (S.sup' hS fun Q ω =>
      mixedBridgeRootHistoryProfile M m t ω Q) :=
    Finset.measurable_sup' (s := S) (hs := hS)
      (f := fun (Q : TriadicCube 2) (ω : Cutoff.CutoffSample 2) =>
        mixedBridgeRootHistoryProfile M m t ω Q)
      (fun Q _ => hroot Q)
  have heq : (fun ω : Cutoff.CutoffSample 2 => mixedBridgeBstar M m t ω) =
      S.sup' hS (fun Q ω => mixedBridgeRootHistoryProfile M m t ω Q) := by
    funext ω
    change Book.Ch02.finsetSupReal S _ = _
    rw [Homogenization.Book.Ch04.RestrictionLawCarrier.finsetSupReal_eq_sup' S hS]
    simp only [Finset.sup'_apply]
  change Measurable (fun ω => mixedBridgeBstar M m t ω)
  rw [heq]
  exact hsup

private theorem parent_gap_responseCoefficient_measurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) :
    Measurable (mixedBridgeResponseCoefficient m t) := by
  let Q := originCube 2 m
  let K := closure (cubeSet Q)
  let U := openCubeSet Q
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (isBounded_cubeSet Q).isCompact_closure
  letI : CompactSpace (closure U) := isCompact_iff_compactSpace.mp
    (isBounded_openCubeSet Q).isCompact_closure
  obtain ⟨ell, hKell⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet Q).isCompact_closure
  let incl : C(closure U, K) :=
    ⟨fun x => ⟨x.1, closure_mono (openCubeSet_subset_cubeSet Q) x.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hFresh : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      shellFieldScalarRestriction K (ω.1 (m + 1))) :=
    (measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply (m + 1)).comp measurable_subtype_coe)
  have hOlder : Measurable (fun ω : Cutoff.CutoffSample 2 => olderField K m ω) :=
    measurable_olderField K ell m hKell
  let f : Cutoff.CutoffSample 2 → C(K, ℝ) := fun ω => modelInsertedScalar K m t ω
  have hf : Measurable f := by
    change Measurable (fun ω => olderField K m ω +
      Real.sqrt t • shellFieldScalarRestriction K (ω.1 (m + 1)))
    have hsqrt : Measurable (fun _ : Cutoff.CutoffSample 2 => Real.sqrt t) :=
      measurable_const
    exact hOlder.add (hsqrt.smul hFresh)
  let g : C(K, ℝ) → ResponseCoefficient U := fun v =>
    BoundedContinuousFunction.mkOfCompact (v.comp incl)
  have hg : Continuous g := by
    unfold g
    exact (ContinuousMap.isometryEquivBoundedOfCompact (closure U) ℝ).continuous.comp
      (by fun_prop)
  have hcomp : Measurable (fun ω => g (f ω)) := hg.measurable.comp hf
  have heq : (fun ω => g (f ω)) = mixedBridgeResponseCoefficient m t := by
    funext ω
    rfl
  rw [← heq]
  exact hcomp

private theorem parent_gap_bilin_polarization {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hB : ∀ x y, B x y = B y x)
    (x y : V) : 4 * B x y = B (x + y) (x + y) - B (x - y) (x - y) := by
  have hp : B (x + y) (x + y) = B x x + B x y + B y x + B y y := by
    rw [B.map_add₂]
    rw [(B x).map_add, (B y).map_add]
    ring
  have hm : B (x - y) (x - y) = B x x - B x y - B y x + B y y := by
    rw [B.map_sub₂]
    rw [(B x).map_sub, (B y).map_sub]
    ring
  rw [hp, hm, hB y x]
  ring

private noncomputable def parent_gap_pullbackBilin {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (T : V →L[ℝ] V) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  ((ContinuousLinearMap.precompR V B).flip T).comp T

private theorem parent_gap_scalarFrame_energyBilin_eq_pullback
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (scalarFrameRealization Q ν σ hν hσ k).energyBilin =
      parent_gap_pullbackBilin
        (scalarFrameRealization Q ν σ hν hσ
          (0 : ResponseCoefficient (openCubeSet Q))).energyBilin
        (1 + responseShearL2Operator σ hσ k) := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let Bk := (scalarFrameRealization Q ν σ hν hσ k).energyBilin
  let B0 := (scalarFrameRealization Q ν σ hν hσ
    (0 : ResponseCoefficient (openCubeSet Q))).energyBilin
  let T := (1 : HilbertBlockL2 (openCubeSet Q) →L[ℝ] HilbertBlockL2 (openCubeSet Q)) +
    responseShearL2Operator σ hσ k
  have hBk : ∀ x y, Bk x y = Bk y x :=
    (scalarFrameRealization Q ν σ hν hσ k).energySymm
  have hB0 : ∀ x y, B0 x y = B0 y x :=
    (scalarFrameRealization Q ν σ hν hσ
      (0 : ResponseCoefficient (openCubeSet Q))).energySymm
  have hdiag (x : HilbertBlockL2 (openCubeSet Q)) : Bk x x = B0 (T x) (T x) := by
    change (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k).toMuHilbertRealization.energyBilin x x =
      (responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
        (0 : ResponseCoefficient (openCubeSet Q))).toMuHilbertRealization.energyBilin
        (T x) (T x)
    have hs := responseFrameMu_energy_shear_identity hU hvol ν σ hν hσ
      (0 : ResponseCoefficient (openCubeSet Q)) k x
    rw [zero_add] at hs
    have hT : T x = x + responseShearL2Operator σ hσ k x := by simp [T]
    simpa only [hT] using hs.symm
  have hpair (x y : HilbertBlockL2 (openCubeSet Q)) :
      Bk x y = B0 (T x) (T y) := by
    have hl := parent_gap_bilin_polarization Bk hBk x y
    have hr := parent_gap_bilin_polarization B0 hB0 (T x) (T y)
    have hadd : T (x + y) = T x + T y := T.map_add x y
    have hsub : T (x - y) = T x - T y := T.map_sub x y
    rw [hdiag (x + y), hdiag (x - y)] at hl
    rw [hadd, hsub] at hl
    calc
      Bk x y = (4 * Bk x y) / 4 := by ring
      _ = (4 * B0 (T x) (T y)) / 4 := by rw [hl, ← hr]
      _ = B0 (T x) (T y) := by ring
  ext x y
  change Bk x y = B0 (T x) (T y)
  exact hpair x y

private theorem parent_gap_continuous_pullbackBilin {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V →L[ℝ] V →L[ℝ] ℝ) :
    Continuous fun T : V →L[ℝ] V => parent_gap_pullbackBilin B T := by
  fun_prop [parent_gap_pullbackBilin]

private theorem parent_gap_continuous_scalarFrame_energyBilin
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) :
    Continuous fun k : ResponseCoefficient (openCubeSet Q) =>
      (scalarFrameRealization Q ν σ hν hσ k).energyBilin := by
  let U := openCubeSet Q
  let B0 := (scalarFrameRealization Q ν σ hν hσ
    (0 : ResponseCoefficient U)).energyBilin
  have hS : Continuous fun k : ResponseCoefficient U =>
      responseShearL2Operator σ hσ k :=
    (responseShearL2Family (measurableSet_openCubeSet Q) σ hσ).continuous
  have hT : Continuous fun k : ResponseCoefficient U =>
      (1 : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) + responseShearL2Operator σ hσ k :=
    continuous_const.add hS
  have hPull : Continuous fun T : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U =>
      parent_gap_pullbackBilin B0 T := parent_gap_continuous_pullbackBilin B0
  have hCont := hPull.comp hT
  have heq : (fun k : ResponseCoefficient U =>
      (scalarFrameRealization Q ν σ hν hσ k).energyBilin) =
    fun k => parent_gap_pullbackBilin B0
      ((1 : HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) +
        responseShearL2Operator σ hσ k) := by
    funext k
    exact parent_gap_scalarFrame_energyBilin_eq_pullback Q ν σ hν hσ k
  rw [heq]
  exact hCont

private theorem parent_gap_scalarFrame_correctionSpace_eq_zero
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    (scalarFrameRealization Q ν σ hν hσ k).correctionSpace.correctionSpace =
      (scalarFrameRealization Q ν σ hν hσ
        (0 : ResponseCoefficient (openCubeSet Q))).correctionSpace.correctionSpace := by
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume (openCubeSet Q)).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let M₁ := responseFrameMuOperatorSystemData hU hvol ν σ hν hσ k
  let M₀ := responseFrameMuOperatorSystemData hU hvol ν σ hν hσ
    (0 : ResponseCoefficient (openCubeSet Q))
  have hsys : M₁.toMuHilbertRealization.correctionSpace =
      M₀.toMuHilbertRealization.correctionSpace := by
    change (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q)).toMuCorrectionSpaceData =
      (PotentialSolenoidalL2Data.ofSubmoduleClosures (openCubeSet Q)).toMuCorrectionSpaceData
    rfl
  change M₁.toMuHilbertRealization.correctionSpace.correctionSpace =
    M₀.toMuHilbertRealization.correctionSpace.correctionSpace
  rw [hsys]

private noncomputable def parent_gap_restrictBilinCLM {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : ClosedSubmodule ℝ V) :
    (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] K.toSubmodule →L[ℝ] ℝ) := by
  let i : K.toSubmodule →L[ℝ] V := K.toSubmodule.subtypeL
  let hOuter : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] V →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ K.toSubmodule V (V →L[ℝ] ℝ)).flip i
  let hInner : (V →L[ℝ] ℝ) →L[ℝ] (K.toSubmodule →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ K.toSubmodule V ℝ).flip i
  exact (ContinuousLinearMap.compL ℝ K.toSubmodule
    (V →L[ℝ] ℝ) (K.toSubmodule →L[ℝ] ℝ) hInner).comp hOuter

private theorem parent_gap_restrictBilinCLM_apply {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    parent_gap_restrictBilinCLM K B = Homogenization.restrictBilin K B := by
  ext x y
  rfl

private noncomputable def parent_gap_restrictedBilinOperatorCLM {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) :
    (K.toSubmodule →L[ℝ] K.toSubmodule →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] K.toSubmodule) :=
  ContinuousLinearMap.compL ℝ K.toSubmodule (K.toSubmodule →L[ℝ] ℝ)
    K.toSubmodule
    (((InnerProductSpace.toDual ℝ K.toSubmodule).symm).toContinuousLinearEquiv
      |>.toContinuousLinearMap)

private theorem parent_gap_restrictedBilinOperatorCLM_apply {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    parent_gap_restrictedBilinOperatorCLM K
      (parent_gap_restrictBilinCLM K B) =
        InnerProductSpace.continuousLinearMapOfBilin
          (Homogenization.restrictBilin K B) := by
  simp [parent_gap_restrictedBilinOperatorCLM,
    InnerProductSpace.continuousLinearMapOfBilin,
    parent_gap_restrictBilinCLM_apply]

private noncomputable def parent_gap_subspaceRhsCLM {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) (x : V) :
    (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] K.toSubmodule := by
  let i : K.toSubmodule →L[ℝ] V := K.toSubmodule.subtypeL
  let eval : (V →L[ℝ] V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) :=
    ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) x
  let restrict : (V →L[ℝ] ℝ) →L[ℝ] (K.toSubmodule →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ K.toSubmodule V ℝ).flip i
  let neg : (K.toSubmodule →L[ℝ] ℝ) →L[ℝ] (K.toSubmodule →L[ℝ] ℝ) := -1
  exact (Homogenization.subspaceRieszMap K).comp (neg.comp (restrict.comp eval))

private theorem parent_gap_subspaceRhsCLM_apply {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (K : ClosedSubmodule ℝ V) (x : V) (B : V →L[ℝ] V →L[ℝ] ℝ) :
    parent_gap_subspaceRhsCLM K x B = Homogenization.subspaceRhs K B x := by
  apply congrArg (Homogenization.subspaceRieszMap K)
  ext y
  simp [Homogenization.subspaceRhsBilin_apply]

private theorem parent_gap_scalarProjectionResidual_measurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (F : HilbertBlockL2 (openCubeSet (originCube 2 m))) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      scalarProjectionResidual (originCube 2 m) M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mixedBridgeResponseCoefficient m t ω) F) := by
  let Q := originCube 2 m
  let U := openCubeSet Q
  let ν := M.nu
  let σ : ℝ := Annealed.sigmaBar M m
  let hν : 0 < ν := M.nu_pos
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  letI finiteEnergyVolume : IsFiniteMeasure (volumeMeasureOn U) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let coeff : Cutoff.CutoffSample 2 → ResponseCoefficient U :=
    mixedBridgeResponseCoefficient m t
  let B : Cutoff.CutoffSample 2 → HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ :=
    fun ω => (scalarFrameRealization Q ν σ hν hσ (coeff ω)).energyBilin
  let hCoercive : ∀ ω, IsCoercive (B ω) := fun ω =>
    (scalarFrameRealization Q ν σ hν hσ (coeff ω)).energyCoercive
  let M₀ := scalarFrameRealization Q ν σ hν hσ (0 : ResponseCoefficient U)
  let K := M₀.correctionSpace.correctionSpace
  letI : IsSeparable (volumeMeasureOn U) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 U) := inferInstance
  letI : BorelSpace K.toSubmodule := inferInstance
  letI : SecondCountableTopology K.toSubmodule := inferInstance
  have hProduct : OpensMeasurableSpace
      ((K.toSubmodule →L[ℝ] K.toSubmodule) × K.toSubmodule) := inferInstance
  have hk : Measurable coeff := parent_gap_responseCoefficient_measurable M m t
  have hB : Measurable B := by
    have hc := parent_gap_continuous_scalarFrame_energyBilin Q ν σ hν hσ
    exact hc.measurable.comp hk
  let sharpMap : (HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ) →L[ℝ]
      (K.toSubmodule →L[ℝ] K.toSubmodule) :=
    (parent_gap_restrictedBilinOperatorCLM K).comp
      (parent_gap_restrictBilinCLM K)
  have hSharp : Measurable fun ω =>
      InnerProductSpace.continuousLinearMapOfBilin
        (Homogenization.restrictBilin K (B ω)) := by
    have hm : Measurable fun ω => sharpMap (B ω) :=
      sharpMap.continuous.measurable.comp hB
    have heq : (fun ω => sharpMap (B ω)) = fun ω =>
        InnerProductSpace.continuousLinearMapOfBilin
          (Homogenization.restrictBilin K (B ω)) := by
      funext ω
      exact parent_gap_restrictedBilinOperatorCLM_apply K (B ω)
    rw [← heq]
    exact hm
  let rhsMap : (HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U →L[ℝ] ℝ) →L[ℝ]
      K.toSubmodule := parent_gap_subspaceRhsCLM K F
  have hRhs : Measurable fun ω => Homogenization.subspaceRhs K (B ω) F := by
    have hm : Measurable fun ω => rhsMap (B ω) :=
      rhsMap.continuous.measurable.comp hB
    have heq : (fun ω => rhsMap (B ω)) = fun ω =>
        Homogenization.subspaceRhs K (B ω) F := by
      funext ω
      exact parent_gap_subspaceRhsCLM_apply K F (B ω)
    rw [← heq]
    exact hm
  have hMin : Measurable fun ω =>
      Homogenization.affineMinimizerMap K (B ω) (hCoercive ω) F :=
    Measurable.affineMinimizerMap_apply (K := K) (hB := hCoercive)
      (x := fun _ => F) measurable_const hSharp hRhs
  have hEq : (fun ω => scalarProjectionResidual Q ν σ hν hσ (coeff ω) F) =
      fun ω => Homogenization.affineMinimizerMap K (B ω) (hCoercive ω) F := by
    funext ω
    rw [scalarProjectionResidual_eq_affineMinimizer]
    rw [parent_gap_scalarFrame_correctionSpace_eq_zero Q ν σ hν hσ (coeff ω)]
  rw [hEq]
  exact hMin

private theorem parent_gap_oldSignedFrameCanonicalField_measurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (P : BlockVec 2) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      oldSignedFrameCanonicalField (originCube 2 m) M.nu
        (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mixedBridgeResponseCoefficient m t ω) P) := by
  let Q := originCube 2 m
  let U := openCubeSet Q
  let ν := M.nu
  let σ : ℝ := Annealed.sigmaBar M m
  let hν : 0 < ν := M.nu_pos
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let coeff : Cutoff.CutoffSample 2 → ResponseCoefficient U :=
    mixedBridgeResponseCoefficient m t
  let F : HilbertBlockL2 U := blockVecToHilbertBlockL2Const P
  have hResidual : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      scalarProjectionResidual Q ν σ hν hσ (coeff ω) F) :=
    parent_gap_scalarProjectionResidual_measurable M m t F
  have hField : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      hilbertBlockL2ToBlockL2 (scalarProjectionResidual Q ν σ hν hσ (coeff ω) F)) :=
    (hilbertBlockL2ToBlockL2 (U := U)).continuous.measurable.comp hResidual
  have hConst (ω : Cutoff.CutoffSample 2) :
      (scalarFrameRealization Q ν σ hν hσ (coeff ω)).constantField P = F := by
    change blockVecToHilbertBlockL2Const P = blockVecToHilbertBlockL2Const P
    rfl
  have hEq :
      (fun ω : Cutoff.CutoffSample 2 => oldSignedFrameCanonicalField Q ν σ hν hσ
        (coeff ω) P) =
      fun ω => hilbertBlockL2ToBlockL2
        (scalarProjectionResidual Q ν σ hν hσ (coeff ω) F) := by
    funext ω
    change oldSignedCanonicalAffineField Q
      (responseFramePlanarCoefficientField ν σ (coeff ω))
      (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
        ν σ hν hσ (coeff ω)) P = _
    rw [← old_signed_affine_residual_field Q ν σ hν hσ (coeff ω) P]
    rw [hConst ω]
    rfl
  rw [hEq]
  exact hField

private theorem parent_gap_potentialCoordinate_ae
    (Q : TriadicCube 2) (i : Fin 2)
    (X : HilbertBlockL2 (openCubeSet Q)) :
    hilbertVectorL2_normalizedCoordCLM Q i
        (hilbertBlockL2PotentialCLM X) =ᵐ[normalizedCubeMeasure Q]
      fun x => (hilbertBlockL2ToBlockL2 X x).1 i := by
  have hcoord := hilbertVectorL2_normalizedCoordCLM_ae Q i
    (hilbertBlockL2PotentialCLM X)
  have hraw : hilbertVectorL2ToVectorL2 (hilbertBlockL2PotentialCLM X) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => (hilbertBlockL2ToBlockL2 X x).1 := by
    filter_upwards [coeFn_hilbertVectorL2ToVectorL2 (hilbertBlockL2PotentialCLM X),
      coeFn_hilbertBlockL2PotentialCLM X, coeFn_hilbertBlockL2ToBlockL2 X] with x hvec hpot hblock
    rw [hvec, hpot, hblock]
  have hdom : normalizedCubeMeasure Q ≤
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volumeMeasureOn (openCubeSet Q) := by
    rw [normalizedCubeMeasure_eq_smul_open Q]
  have habs : normalizedCubeMeasure Q ≪ volumeMeasureOn (openCubeSet Q) :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hraw' : hilbertVectorL2ToVectorL2 (hilbertBlockL2PotentialCLM X) =ᵐ[
      normalizedCubeMeasure Q]
      fun x => (hilbertBlockL2ToBlockL2 X x).1 := habs.ae_eq hraw
  have hrawi := hraw'.mono (fun x hx => congrArg (fun v : Vec 2 => v i) hx)
  exact hcoord.trans hrawi

private theorem parent_gap_fluxCoordinate_ae
    (Q : TriadicCube 2) (i : Fin 2)
    (X : HilbertBlockL2 (openCubeSet Q)) :
    hilbertVectorL2_normalizedCoordCLM Q i
        (hilbertBlockL2FluxCLM X) =ᵐ[normalizedCubeMeasure Q]
      fun x => (hilbertBlockL2ToBlockL2 X x).2 i := by
  have hcoord := hilbertVectorL2_normalizedCoordCLM_ae Q i
    (hilbertBlockL2FluxCLM X)
  have hraw : hilbertVectorL2ToVectorL2 (hilbertBlockL2FluxCLM X) =ᵐ[
      volumeMeasureOn (openCubeSet Q)]
      fun x => (hilbertBlockL2ToBlockL2 X x).2 := by
    filter_upwards [coeFn_hilbertVectorL2ToVectorL2 (hilbertBlockL2FluxCLM X),
      coeFn_hilbertBlockL2FluxCLM X, coeFn_hilbertBlockL2ToBlockL2 X] with x hvec hflux hblock
    rw [hvec, hflux, hblock]
  have hdom : normalizedCubeMeasure Q ≤
      ENNReal.ofReal ((cubeVolume Q)⁻¹) • volumeMeasureOn (openCubeSet Q) := by
    rw [normalizedCubeMeasure_eq_smul_open Q]
  have habs : normalizedCubeMeasure Q ≪ volumeMeasureOn (openCubeSet Q) :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hraw' : hilbertVectorL2ToVectorL2 (hilbertBlockL2FluxCLM X) =ᵐ[
      normalizedCubeMeasure Q]
      fun x => (hilbertBlockL2ToBlockL2 X x).2 := habs.ae_eq hraw
  have hrawi := hraw'.mono (fun x hx => congrArg (fun v : Vec 2 => v i) hx)
  exact hcoord.trans hrawi

private theorem parent_gap_dualEnergy_congr_ae
    (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hfg : f =ᵐ[normalizedCubeMeasure Q] g) :
    dualEnergy Q (Real.sqrt 3) f = dualEnergy Q (Real.sqrt 3) g := by
  have hraw : volumeMeasureOn (openCubeSet Q) =
      ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    rw [normalizedCubeMeasure_eq_smul_open Q, smul_smul]
    have hcoeff : ENNReal.ofReal (cubeVolume Q) *
        ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul (cubeVolume_pos Q).le]
      rw [mul_inv_cancel₀ (ne_of_gt (cubeVolume_pos Q)), ENNReal.ofReal_one]
    rw [hcoeff, one_smul]
  have hdom : volume.restrict (cubeSet Q) ≤
      ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
    exact le_of_eq hraw
  have habs : volume.restrict (cubeSet Q) ≪ normalizedCubeMeasure Q :=
    Measure.absolutelyContinuous_of_le_smul hdom
  have hfg' : f =ᵐ[volume.restrict (cubeSet Q)] g := habs.ae_eq hfg
  have hinc (j : ℕ) := diagCubeIncrement_congr_ae Q j hfg'
  unfold dualEnergy primalEnergy
  simp_rw [hinc]

private theorem parent_gap_vCoordinate_ae
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (a : BlockCoord 2) (i : Fin 2) :
    let Q := originCube 2 m
    let ν := M.nu
    let σ : ℝ := Annealed.sigmaBar M m
    let hν : 0 < ν := M.nu_pos
    let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
    let k := mixedBridgeResponseCoefficient m t ω
    let X := blockL2ToHilbertBlockL2
      (oldSignedFrameCanonicalField Q ν σ hν hσ k (blockBasis a))
    (hilbertVectorL2_normalizedCoordCLM Q i
      (hilbertBlockL2PotentialCLM X) -
        Lp.const 2 (normalizedCubeMeasure Q) ((blockBasis a).1 i)) =ᵐ[
      normalizedCubeMeasure Q]
      fun x => ((oldSignedFrameCanonicalField Q ν σ hν hσ k
        (blockBasis a) x).1 - (blockBasis a).1) i := by
  dsimp only
  let Q := originCube 2 m
  let ν := M.nu
  let σ : ℝ := Annealed.sigmaBar M m
  let hν : 0 < ν := M.nu_pos
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let k := mixedBridgeResponseCoefficient m t ω
  let F := oldSignedFrameCanonicalField Q ν σ hν hσ k (blockBasis a)
  let X := blockL2ToHilbertBlockL2 F
  have hX : hilbertBlockL2ToBlockL2 X = F :=
    hilbertBlockL2ToBlockL2_blockL2ToHilbertBlockL2 F
  have hpot := parent_gap_potentialCoordinate_ae Q i X
  have hpot' : hilbertVectorL2_normalizedCoordCLM Q i
      (hilbertBlockL2PotentialCLM X) =ᵐ[normalizedCubeMeasure Q]
        fun x => (F x).1 i := by
    rw [hX] at hpot
    exact hpot
  filter_upwards [Lp.coeFn_sub
      (hilbertVectorL2_normalizedCoordCLM Q i (hilbertBlockL2PotentialCLM X))
      (Lp.const 2 (normalizedCubeMeasure Q) ((blockBasis a).1 i)),
    Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := normalizedCubeMeasure Q)
      (c := ((blockBasis a).1 i)), hpot'] with x hsub hconst hfield
  calc
    (hilbertVectorL2_normalizedCoordCLM Q i
        (hilbertBlockL2PotentialCLM X) -
          Lp.const 2 (normalizedCubeMeasure Q) ((blockBasis a).1 i) :
        Lp ℝ 2 (normalizedCubeMeasure Q)) x =
        hilbertVectorL2_normalizedCoordCLM Q i
          (hilbertBlockL2PotentialCLM X) x -
          (Lp.const 2 (normalizedCubeMeasure Q) ((blockBasis a).1 i) :
            Lp ℝ 2 (normalizedCubeMeasure Q)) x := hsub
    _ = (F x).1 i - (blockBasis a).1 i := by
      rw [hfield, hconst]
      simp
    _ = ((F x).1 - (blockBasis a).1) i := rfl

private theorem parent_gap_primalEnergy_measurable_of_l2_map
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : TriadicCube 2)
    [MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [BorelSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    (q : ℝ) (hq : 0 ≤ q)
    (u : Ω → Lp ℝ 2 (normalizedCubeMeasure Q))
    (hu : Measurable u) :
    Measurable (fun ω => primalEnergy Q q (fun x => u ω x)) := by
  classical
  let a : ℕ → Ω → ℝ := fun n ω =>
    q ^ (n + 1) * ‖cubeIncrementL2CLM Q (n + 1) (u ω)‖ ^ 2
  let S : Ω → ENNReal := fun ω => ∑' n, ENNReal.ofReal (a n ω)
  have ha (n : ℕ) : Measurable (a n) := by
    dsimp [a]
    have hn : Measurable (fun ω =>
        ‖cubeIncrementL2CLM Q (n + 1) (u ω)‖ ^ 2) :=
      (((cubeIncrementL2CLM Q (n + 1)).continuous.measurable.comp hu).norm.pow_const 2)
    simpa only [mul_comm] using hn.const_mul (q ^ (n + 1))
  have ha_nonneg (n : ℕ) (ω : Ω) : 0 ≤ a n ω := by
    dsimp [a]
    exact mul_nonneg (pow_nonneg hq _) (sq_nonneg _)
  have hS : Measurable S := by
    dsimp [S]
    exact Measurable.ennreal_tsum fun n => (ha n).ennreal_ofReal
  have htsum (ω : Ω) : (∑' n, a n ω) = (S ω).toReal := by
    by_cases htop : S ω = ∞
    · have hnot : ¬ Summable (fun n => a n ω) := by
        intro hs
        have hfinite := hs.tsum_ofReal_ne_top
        have hSfinite : S ω ≠ ∞ := by
          intro hInf
          exact hfinite (by simpa [S] using hInf)
        exact hSfinite htop
      rw [tsum_eq_zero_of_not_summable hnot, htop]
      rfl
    · let b : ℕ → NNReal := fun n => Real.toNNReal (a n ω)
      have hb (n : ℕ) : (b n : ENNReal) = ENNReal.ofReal (a n ω) := by
        simp [b, ENNReal.ofReal, Real.toNNReal_of_nonneg (ha_nonneg n ω)]
      have hsumB : Summable b := by
        apply (ENNReal.tsum_coe_ne_top_iff_summable).mp
        rw [show (∑' n, (b n : ENNReal)) = S ω from by
          apply tsum_congr
          intro n
          exact hb n]
        exact htop
      have hsumA : Summable (fun n => a n ω) := by
        have hsumReal : Summable (fun n => (b n : ℝ)) := NNReal.summable_coe.2 hsumB
        have hEq : (fun n => (b n : ℝ)) = fun n => a n ω := by
          funext n
          dsimp [b]
          exact Real.coe_toNNReal _ (ha_nonneg n ω)
        exact hEq ▸ hsumReal
      have hrepr : ENNReal.ofReal (∑' n, a n ω) = S ω := by
        dsimp [S]
        exact ENNReal.ofReal_tsum_of_nonneg (fun n => ha_nonneg n ω) hsumA
      have hsum_nonneg : 0 ≤ (∑' n, a n ω) := tsum_nonneg fun n => ha_nonneg n ω
      calc
        (∑' n, a n ω) = (ENNReal.ofReal (∑' n, a n ω)).toReal := by
          rw [ENNReal.toReal_ofReal hsum_nonneg]
        _ = (S ω).toReal := by rw [hrepr]
  have hbaseEq :
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x))) =
        fun ω => ‖cubeIncrementL2CLM Q 0 (u ω)‖ ^ 2 := by
    funext ω
    exact energy_cubeIncrement_eq_clm_norm_sq Q 0 (u ω)
  have hbase : Measurable
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x))) := by
    rw [hbaseEq]
    exact (((cubeIncrementL2CLM Q 0).continuous.measurable.comp hu).norm.pow_const 2)
  have hEq (ω : Ω) : primalEnergy Q q (fun x => u ω x) =
      energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal := by
    rw [primalEnergy]
    have hterm (n : ℕ) : q ^ (n + 1) * energy Q
        (cubeIncrement Q (n + 1) (fun x => u ω x)) = a n ω := by
      rw [energy_cubeIncrement_eq_clm_norm_sq]
    rw [tsum_congr hterm, htsum ω]
  have hresult : Measurable
      (fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal) :=
    hbase.add hS.ennreal_toReal
  rw [show (fun ω => primalEnergy Q q (fun x => u ω x)) =
      fun ω => energy Q (cubeIncrement Q 0 (fun x => u ω x)) + (S ω).toReal from by
        funext ω
        exact hEq ω]
  exact hresult

private theorem parent_gap_dualEnergy_measurable_of_l2_map
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : TriadicCube 2)
    [MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [BorelSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    [OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q))]
    (u : Ω → Lp ℝ 2 (normalizedCubeMeasure Q))
    (hu : Measurable u) :
    Measurable (fun ω => dualEnergy Q (Real.sqrt 3) (fun x => u ω x)) := by
  unfold dualEnergy
  exact parent_gap_primalEnergy_measurable_of_l2_map Q
    ((Real.sqrt 3)⁻¹) (inv_nonneg.mpr (Real.sqrt_nonneg _)) u hu

private theorem parent_gap_v2_measurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 => mixedBridgeV2 M m t ω) := by
  classical
  let Q := originCube 2 m
  let U := openCubeSet Q
  let ν := M.nu
  let σ : ℝ := Annealed.sigmaBar M m
  let hν : 0 < ν := M.nu_pos
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let coeff : Cutoff.CutoffSample 2 → ResponseCoefficient U :=
    mixedBridgeResponseCoefficient m t
  let can (a : BlockCoord 2) (ω : Cutoff.CutoffSample 2) : BlockL2 U :=
    oldSignedFrameCanonicalField Q ν σ hν hσ (coeff ω) (blockBasis a)
  let X (a : BlockCoord 2) (ω : Cutoff.CutoffSample 2) : HilbertBlockL2 U :=
    blockL2ToHilbertBlockL2 (can a ω)
  let u (a : BlockCoord 2) (i : Fin 2) (ω : Cutoff.CutoffSample 2) :
      Lp ℝ 2 (normalizedCubeMeasure Q) :=
    hilbertVectorL2_normalizedCoordCLM Q i
      (hilbertBlockL2PotentialCLM (X a ω)) -
        Lp.const 2 (normalizedCubeMeasure Q) ((blockBasis a).1 i)
  letI : MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q)) := borel _
  letI : BorelSpace (Lp ℝ 2 (normalizedCubeMeasure Q)) := ⟨rfl⟩
  letI : OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q)) := ⟨le_of_eq rfl⟩
  letI : IsSeparable (volumeMeasureOn U) := inferInstance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 U) := inferInstance
  have hcan (a : BlockCoord 2) : Measurable (can a) :=
    parent_gap_oldSignedFrameCanonicalField_measurable M m t (blockBasis a)
  have hX (a : BlockCoord 2) : Measurable (X a) := by
    exact (blockL2ToHilbertBlockL2 (U := U)).continuous.measurable.comp (hcan a)
  have hCoord (a : BlockCoord 2) (i : Fin 2) :
      Measurable (fun ω => hilbertVectorL2_normalizedCoordCLM Q i
        (hilbertBlockL2PotentialCLM (X a ω))) := by
    exact (hilbertVectorL2_normalizedCoordCLM Q i).continuous.measurable.comp
      ((hilbertBlockL2PotentialCLM (U := U)).continuous.measurable.comp (hX a))
  have hu (a : BlockCoord 2) (i : Fin 2) : Measurable (u a i) := by
    dsimp [u]
    exact (hCoord a i).sub measurable_const
  have hdual (a : BlockCoord 2) (i : Fin 2) :
      Measurable (fun ω => dualEnergy Q (Real.sqrt 3) (fun x => u a i ω x)) :=
    parent_gap_dualEnergy_measurable_of_l2_map Q (u a i) (hu a i)
  have hcoordinateIdentity (ω : Cutoff.CutoffSample 2) (a : BlockCoord 2) :
      vectorWeakHaarNorm Q (fun x => (can a ω x).1 - (blockBasis a).1) ^ 2 =
        ∑ i : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => u a i ω x) := by
    rw [vectorWeakHaarNorm_sq]
    apply Finset.sum_congr rfl
    intro j hj
    have hAE := parent_gap_vCoordinate_ae M m t ω a j
    have hAE' : u a j ω =ᵐ[normalizedCubeMeasure Q]
        fun x => ((can a ω x).1 - (blockBasis a).1) j := by
      simpa [u, X, can, coeff, Q, ν, σ, hν, hσ] using hAE
    have hde := parent_gap_dualEnergy_congr_ae Q hAE'.symm
    change weakHaarNorm Q (fun x => ((can a ω x).1 - (blockBasis a).1) j) ^ 2 = _
    rw [weakHaarNorm, Real.sq_sqrt (dualEnergy_nonneg Q (Real.sqrt 3)
      (Real.sqrt_nonneg _) (fun x => ((can a ω x).1 - (blockBasis a).1) j))]
    exact hde
  have hsum : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      ∑ a : BlockCoord 2, ∑ i : Fin 2,
        dualEnergy Q (Real.sqrt 3) (fun x => u a i ω x)) := by
    apply Finset.measurable_sum
    intro a ha
    apply Finset.measurable_sum
    intro i hi
    exact hdual a i
  have hEq : (fun ω : Cutoff.CutoffSample 2 => mixedBridgeV2 M m t ω) =
      fun ω => ∑ a : BlockCoord 2, ∑ i : Fin 2,
        dualEnergy Q (Real.sqrt 3) (fun x => u a i ω x) := by
    funext ω
    simp only [mixedBridgeV2, oldSignedPrimalErrorSize]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun a ha => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro a ha
    exact hcoordinateIdentity ω a
  rw [hEq]
  exact hsum

private theorem parent_gap_measurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 => mixedBridge M m t ω) := by
  classical
  let Q := originCube 2 m
  let U := openCubeSet Q
  let ν := M.nu
  let σ : ℝ := Annealed.sigmaBar M m
  let hν : 0 < ν := M.nu_pos
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  let coeff : Cutoff.CutoffSample 2 → ResponseCoefficient U :=
    mixedBridgeResponseCoefficient m t
  let can (a : BlockCoord 2) (ω : Cutoff.CutoffSample 2) : BlockL2 U :=
    oldSignedFrameCanonicalField Q ν σ hν hσ (coeff ω) (blockBasis a)
  let X (a : BlockCoord 2) (ω : Cutoff.CutoffSample 2) : HilbertBlockL2 U :=
    blockL2ToHilbertBlockL2 (can a ω)
  let T (a : BlockCoord 2) (ω : Cutoff.CutoffSample 2) : HilbertBlockL2 U :=
    X a ω + responseShearL2Operator σ hσ (coeff ω) (X a ω)
  let u (a : BlockCoord 2) (i : Fin 2) (ω : Cutoff.CutoffSample 2) :
      Lp ℝ 2 (normalizedCubeMeasure Q) :=
    (σ / ν) • hilbertVectorL2_normalizedCoordCLM Q i
        (hilbertBlockL2FluxCLM (T a ω)) -
      Lp.const 2 (normalizedCubeMeasure Q) (((blockBasis a).2) i)
  letI : MeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q)) := borel _
  letI : BorelSpace (Lp ℝ 2 (normalizedCubeMeasure Q)) := ⟨rfl⟩
  letI : OpensMeasurableSpace (Lp ℝ 2 (normalizedCubeMeasure Q)) := ⟨le_of_eq rfl⟩
  letI : IsSeparable (volumeMeasureOn U) := inferInstance
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 U) := inferInstance
  have hcoeff : Measurable coeff := parent_gap_responseCoefficient_measurable M m t
  have hcan (a : BlockCoord 2) : Measurable (can a) :=
    parent_gap_oldSignedFrameCanonicalField_measurable M m t (blockBasis a)
  have hX (a : BlockCoord 2) : Measurable (X a) := by
    exact (blockL2ToHilbertBlockL2 (U := U)).continuous.measurable.comp (hcan a)
  have hOp : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      responseShearL2Operator σ hσ (coeff ω)) := by
    exact (responseShearL2Family (measurableSet_openCubeSet Q) σ hσ).continuous.measurable.comp
      hcoeff
  letI : OpensMeasurableSpace
      ((HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) × HilbertBlockL2 U) := inferInstance
  have hShear (a : BlockCoord 2) : Measurable (fun ω =>
      responseShearL2Operator σ hσ (coeff ω) (X a ω)) := by
    have hev : Continuous fun p : (HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U) ×
        HilbertBlockL2 U => p.1 p.2 := by fun_prop
    exact hev.measurable.comp (hOp.prodMk (hX a))
  have hT (a : BlockCoord 2) : Measurable (T a) := by
    exact (hX a).add (hShear a)
  have hFlux (a : BlockCoord 2) : Measurable (fun ω =>
      hilbertBlockL2FluxCLM (T a ω)) := by
    exact (hilbertBlockL2FluxCLM (U := U)).continuous.measurable.comp (hT a)
  have hCoord (a : BlockCoord 2) (i : Fin 2) : Measurable (fun ω =>
      hilbertVectorL2_normalizedCoordCLM Q i
        (hilbertBlockL2FluxCLM (T a ω))) := by
    exact (hilbertVectorL2_normalizedCoordCLM Q i).continuous.measurable.comp
      (hFlux a)
  have hu (a : BlockCoord 2) (i : Fin 2) : Measurable (u a i) := by
    dsimp [u]
    exact ((hCoord a i).const_smul (σ / ν)).sub measurable_const
  have hdual (a : BlockCoord 2) (i : Fin 2) :
      Measurable (fun ω => dualEnergy Q (Real.sqrt 3) (fun x => u a i ω x)) :=
    parent_gap_dualEnergy_measurable_of_l2_map Q (u a i) (hu a i)
  have hcoordinateAE (ω : Cutoff.CutoffSample 2) (a : BlockCoord 2)
      (i : Fin 2) :
      u a i ω =ᵐ[normalizedCubeMeasure Q]
        fun x => ((blockMatVecMul
          (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
          (can a ω x)).2 - (blockBasis a).2) i := by
    let F := can a ω
    let Xω := X a ω
    let Tω := T a ω
    let W := hilbertBlockL2FluxCLM Tω
    have hFluxCoord := parent_gap_fluxCoordinate_ae Q i Tω
    have hPointwiseShear :
        (fun x => (hilbertBlockL2ToBlockL2 Tω x).2) =ᵐ[
          volumeMeasureOn U]
          fun x => (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (hilbertBlockL2ToBlockL2 Xω x)).2 := by
      have hs := responseShearAffineL2_toBlockL2_ae σ hσ (coeff ω) Xω
      filter_upwards [hs] with x hx
      exact congrArg Prod.snd hx
    have hdom : normalizedCubeMeasure Q ≤
        ENNReal.ofReal ((cubeVolume Q)⁻¹) • volumeMeasureOn U := by
      rw [normalizedCubeMeasure_eq_smul_open Q]
    have habs : normalizedCubeMeasure Q ≪ volumeMeasureOn U :=
      Measure.absolutelyContinuous_of_le_smul hdom
    have hPointwiseShear' :
        (fun x => (hilbertBlockL2ToBlockL2 Tω x).2) =ᵐ[
          normalizedCubeMeasure Q]
          fun x => (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (hilbertBlockL2ToBlockL2 Xω x)).2 := habs.ae_eq hPointwiseShear
    have hflux := hFluxCoord.trans (hPointwiseShear'.mono
      (fun x hx => congrArg (fun v : Vec 2 => v i) hx))
    have hXrep : hilbertBlockL2ToBlockL2 Xω =ᵐ[volumeMeasureOn U] F := by
      rw [hilbertBlockL2ToBlockL2_blockL2ToHilbertBlockL2]
    have hXrep' : hilbertBlockL2ToBlockL2 Xω =ᵐ[normalizedCubeMeasure Q] F :=
      habs.ae_eq hXrep
    have hlower (x : Vec 2) :
        (blockMatVecMul
          (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
          (F x)).2 = lemmaVConjugateGradient ν σ
            (responseCoefficientExtension (coeff ω) x) (F x) := by
      have h := lemmaV_planar_lower_image ν σ
        (responseCoefficientExtension (coeff ω) x) hν hσ (F x)
      simpa [responseFramePlanarCoefficientField, blockCoeffField] using h
    have hShearIdentity (x : Vec 2) :
        lemmaVConjugateGradient ν σ (responseCoefficientExtension (coeff ω) x) (F x) =
          (σ / ν) • (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (F x)).2 := by
      ext j
      simp [lemmaVConjugateGradient, responseShear, responseShearCorrection,
        Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_eq_add_neg]
    have hShearRep :
        (fun x => (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (hilbertBlockL2ToBlockL2 Xω x)).2 i) =ᵐ[normalizedCubeMeasure Q]
          fun x => (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (F x)).2 i := hXrep'.mono (fun x hx => congrArg
              (fun z : BlockVec 2 =>
                (responseShear σ (responseCoefficientExtension (coeff ω) x) z).2 i) hx)
    have hcombine := hflux.trans hShearRep
    have hcombine' :
        (fun x => (σ / ν) *
            hilbertVectorL2_normalizedCoordCLM Q i W x) =ᵐ[
              normalizedCubeMeasure Q]
          fun x => (σ / ν) * (responseShear σ
            (responseCoefficientExtension (coeff ω) x) (F x)).2 i :=
      hcombine.mono (fun x hx => congrArg (fun z : ℝ => (σ / ν) * z) hx)
    have hfinal :
        (σ / ν) • hilbertVectorL2_normalizedCoordCLM Q i W -
            Lp.const 2 (normalizedCubeMeasure Q) (((blockBasis a).2) i) =ᵐ[
              normalizedCubeMeasure Q]
          fun x => ((blockMatVecMul
            (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
            (F x)).2 - (blockBasis a).2) i := by
      filter_upwards [Lp.coeFn_sub
          ((σ / ν) • hilbertVectorL2_normalizedCoordCLM Q i W)
          (Lp.const 2 (normalizedCubeMeasure Q) (((blockBasis a).2) i)),
        Lp.coeFn_smul (σ / ν) (hilbertVectorL2_normalizedCoordCLM Q i W),
        Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := normalizedCubeMeasure Q)
          (c := (((blockBasis a).2) i)), hcombine'] with x hsub hsmul hconst hcomb
      calc
        ((σ / ν) • hilbertVectorL2_normalizedCoordCLM Q i W -
            Lp.const 2 (normalizedCubeMeasure Q) (((blockBasis a).2) i) :
            Lp ℝ 2 (normalizedCubeMeasure Q)) x =
            ((σ / ν) • hilbertVectorL2_normalizedCoordCLM Q i W :
              Lp ℝ 2 (normalizedCubeMeasure Q)) x -
              (Lp.const 2 (normalizedCubeMeasure Q) (((blockBasis a).2) i) :
                Lp ℝ 2 (normalizedCubeMeasure Q)) x := hsub
        _ = (σ / ν) * hilbertVectorL2_normalizedCoordCLM Q i W x -
            ((blockBasis a).2) i := by
          rw [hsmul, hconst]
          simp [smul_eq_mul]
        _ =
          (σ / ν) * (responseShear σ (responseCoefficientExtension (coeff ω) x)
            (F x)).2 i - ((blockBasis a).2) i := by rw [hcomb]
        _ = ((blockMatVecMul
            (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
            (F x)).2 - (blockBasis a).2) i := by
          rw [hlower x, hShearIdentity x]
          simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simpa [u, T, X, can, coeff, Q, U, ν, σ, hν, hσ, W, Tω, Xω, F] using hfinal
  have hcoordinateIdentity (ω : Cutoff.CutoffSample 2) (a : BlockCoord 2) :
      vectorWeakHaarNorm Q (fun x =>
        (blockMatVecMul
          (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
          (can a ω x)).2 - (blockBasis a).2) ^ 2 =
        ∑ i : Fin 2, dualEnergy Q (Real.sqrt 3) (fun x => u a i ω x) := by
    rw [vectorWeakHaarNorm_sq]
    apply Finset.sum_congr rfl
    intro i hi
    have hAE := hcoordinateAE ω a i
    have hde := parent_gap_dualEnergy_congr_ae Q hAE.symm
    change weakHaarNorm Q (fun x =>
      ((blockMatVecMul
        (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
        (can a ω x)).2 - (blockBasis a).2) i) ^ 2 = _
    rw [weakHaarNorm, Real.sq_sqrt (dualEnergy_nonneg Q (Real.sqrt 3)
      (Real.sqrt_nonneg _)
      (fun x => ((blockMatVecMul
        (blockCoeffField (responseFramePlanarCoefficientField ν σ (coeff ω)) x)
        (can a ω x)).2 - (blockBasis a).2) i))]
    exact hde
  have hsum : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      ∑ a : BlockCoord 2, ∑ i : Fin 2,
        dualEnergy Q (Real.sqrt 3) (fun x => u a i ω x)) := by
    apply Finset.measurable_sum
    intro a ha
    apply Finset.measurable_sum
    intro i hi
    exact hdual a i
  have hEq : (fun ω : Cutoff.CutoffSample 2 => mixedBridge M m t ω) =
      fun ω => ∑ a : BlockCoord 2, ∑ i : Fin 2,
        dualEnergy Q (Real.sqrt 3) (fun x => u a i ω x) := by
    funext ω
    simp only [mixedBridge, oldSignedReciprocalErrorSize]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun a ha => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro a ha
    simpa [oldSignedDualReflection, can, coeff, Q, ν, σ, hν, hσ] using
      hcoordinateIdentity ω a
  rw [hEq]
  exact hsum

theorem parent_gap_vg_measurable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 => mixedBridgeV2 M m t ω) ∧
      Measurable (fun ω : Cutoff.CutoffSample 2 => mixedBridge M m t ω) :=
  ⟨parent_gap_v2_measurable M m t, parent_gap_measurable M m t⟩

end ASDExplicitGamma.Inverse


