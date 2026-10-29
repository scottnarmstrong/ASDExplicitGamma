module

public import ASDExplicitGamma.Main.DirectionalCovarianceTrace
public import ASDExplicitGamma.Inverse.MixedBridgeRootTheta
public import ASDExplicitGamma.Native.OldSignedSourceCellFrame
public import ASDExplicitGamma.Native.OldSignedWeakTraceProxySeries
public import Algsuperdiff.Section3.Provider.ErrorComparison.CubeMonotonicity

/-! Pointwise comparison of the actual directional source trace with the
local OLD-Theta carrier on the same source cell and cutoff sample. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse


open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Native
open ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational ASDExplicitGamma.Main ASDExplicitGamma.Cold
open scoped ENNReal

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

private theorem squareCellMean_eq_descendantsAverage
    (Q : TriadicCube 2) (j : ℕ) (f : TriadicCube 2 → ℝ) :
    Cold.squareCellMean Q j (fun C => f C.1) = descendantsAverage Q j f := by
  unfold Cold.squareCellMean descendantsAverage
  congr 1
  exact Finset.sum_attach (descendantsAtDepth Q j) f

private theorem partial_trace_cell_eq_raw
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) (Q : TriadicCube 2)
    (a : CoeffField 2)
    (hfield : ∀ x ∈ openCubeSet Q,
      a x = (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun x)
    (R : TriadicCube 2) (j : ℕ) (hR : R ∈ descendantsAtDepth Q j) :
    traceDefect (openCubeSet R) a 1 = rawCubeFourLoadTrace M m R t ω := by
  have hRsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hae := (ae_restrict_mem (μ := volume) (measurableSet_openCubeSet R)).mono
    (fun x hx => hfield x (hRsub hx))
  have htrace : traceDefect (openCubeSet R) a 1 =
      traceDefect (openCubeSet R)
        ((Annealed.sigmaBar M m : ℝ)⁻¹ •
          (Model.partialInsertedCoefficient M m t ω).toFun) 1 := by
    unfold traceDefect
    rw [coarseBlockMatrix_congr_of_ae_eq hae]
    rfl
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet Q)) (isBounded_cubeSet Q).isCompact_closure
  have hRcube : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
  have hEll := Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
    (measurableSet_cubeSet R) (fun x hx => hK (subset_closure (hRcube hx)))
  have hframe := Cold.cold_trace_frame M.nu_pos hEll
    (Annealed.sigmaBar_characterization M m).1
  change traceDefect (openCubeSet R) a 1 =
    traceDefect (cubeSet R)
      (Model.partialInsertedCoefficient M m t ω).toFun
      (Annealed.sigmaBar M m : ℝ)
  exact htrace.trans hframe

private theorem source_trace_average_eq
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) (Q : TriadicCube 2)
    (a : CoeffField 2)
    (hfield : ∀ x ∈ openCubeSet Q,
      a x = (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun x) (j : ℕ) :
    descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) =
      rawWeakTraceSequence M m Q t ω j := by
  have hcell (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
      traceDefect (openCubeSet R) a 1 = rawCubeFourLoadTrace M m R t ω := by
    exact partial_trace_cell_eq_raw M m t ht ω Q a hfield R j hR
  calc
    descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) =
        descendantsAverage Q j (fun R => rawCubeFourLoadTrace M m R t ω) := by
      unfold descendantsAverage
      dsimp only
      apply congrArg (fun x : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * x)
      apply Finset.sum_congr rfl
      intro R hR
      exact hcell R hR
    _ = rawWeakTraceSequence M m Q t ω j := by
      unfold rawWeakTraceSequence
      exact (squareCellMean_eq_descendantsAverage Q j
        (fun R => rawCubeFourLoadTrace M m R t ω)).symm

private theorem bank_response_max_eq_finsetSup
    (s : Finset (TriadicCube 2)) (hs : s.Nonempty)
    (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    bankFiniteRootResponseMax s M m J weights ω =
      ENNReal.ofReal (Book.Ch02.finsetSupReal s
        (fun R => rootInverseResponse M R m J weights ω)) := by
  classical
  have huniv : (Finset.univ : Finset ↥s) = s.attach := by
    ext R
    simp
  calc
    bankFiniteRootResponseMax s M m J weights ω =
        (Finset.univ : Finset ↥s).sup
          (fun R => ENNReal.ofReal (rootInverseResponse M R.1 m J weights ω)) := by
      simp only [bankFiniteRootResponseMax, historyFiniteMax]
    _ = s.attach.sup
        (fun R => ENNReal.ofReal (rootInverseResponse M R.1 m J weights ω)) := by
      rw [huniv]
    _ = s.sup (fun R => ENNReal.ofReal (rootInverseResponse M R m J weights ω)) := by
      exact Finset.sup_attach s
        (fun R => ENNReal.ofReal (rootInverseResponse M R m J weights ω))
    _ = ENNReal.ofReal (Book.Ch02.finsetSupReal s
        (fun R => rootInverseResponse M R m J weights ω)) :=
      (ennreal_finset_sup_ofReal s hs _).symm

private theorem directional_depth_max_le_global
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) (Q : TriadicCube 2)
    (hQ : Q = originCube 2 (m - 5))
    (a : CoeffField 2)
    {lamA LamA : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA (openCubeSet Q) a)
    (hfield : ∀ x ∈ openCubeSet Q,
      a x = (Annealed.sigmaBar M m : ℝ)⁻¹ •
        (Model.partialInsertedCoefficient M m t ω).toFun x)
    (j : ℕ) :
    lemmaVInverseDepthMax Q a j ≤
      mixedOldDepthCoefficient M m t j ω := by
  classical
  let σ : ℝ := Annealed.sigmaBar M m
  let c : CoeffField 2 := (Model.partialInsertedCoefficient M m t ω).toFun
  let D : Finset (TriadicCube 2) :=
    bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j
  let Y : ℝ := (bankFiniteRootResponseMax D M m (m + 40)
    (bankPartialInsertionWeights m 1 t) ω).toReal
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet Q)) (isBounded_cubeSet Q).isCompact_closure
  have hEllCopen : IsEllipticFieldOn M.nu
      ((2 * 2 * (Model.partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu)
      (openCubeSet Q) c :=
    Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
      (measurableSet_openCubeSet Q)
      (fun x hx => hK (subset_closure (openCubeSet_subset_cubeSet Q hx)))
  have hEllCcube : IsEllipticFieldOn M.nu
      ((2 * 2 * (Model.partialInsertedEntryBound M ell m ω) ^ 2 + M.nu ^ 2) / M.nu)
      (cubeSet Q) c :=
    Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω ht
      (measurableSet_cubeSet Q)
      (fun x hx => hK (subset_closure hx))
  have hmatrix (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
      coarseBlockMatrix (cubeSet R) a =
        frameMatrix σ (coarseBlockMatrix (cubeSet R) c) := by
    have hfieldR : (fun x => a x) =ᵐ[volumeMeasureOn (openCubeSet R)]
        (σ⁻¹ • c) := by
      filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_openCubeSet R)]
        with x hx
      exact hfield x
        (openCubeSet_subset_of_mem_descendantsAtDepth hR hx)
    have hcoarse : coarseBlockMatrix (cubeSet R) a =
        coarseBlockMatrix (cubeSet R) (σ⁻¹ • c) := by
      rw [Cold.cold_coarse_cube_open R a,
        Cold.cold_coarse_cube_open R (σ⁻¹ • c)]
      exact coarseBlockMatrix_congr_of_ae_eq hfieldR
    have hEllR := hEllCcube.mono (measurableSet_cubeSet R)
        (cubeSet_subset_of_mem_descendantsAtDepth hR)
    have hframe := Cold.cold_coarse_frame M.nu_pos hEllR hσ
    exact hcoarse.trans hframe
  have hlocalFrame : lemmaVInverseDepthMax Q a j =
      σ * lemmaVInverseDepthMax Q c j := by
    exact pureFlux_inverseDepthMax_frame_eq Q c a hEllCopen hEllA hσ j hmatrix
  have hcoeff : attenuatedCoefficient M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω = c := by
    dsimp [c]
    calc
      _ = (Model.partialInsertedCoefficient M (m + (1 : ℤ) - 1) t ω).toFun :=
        bank_one_pass_partial_coefficient M m 1 (by norm_num) t ω
      _ = _ := by rw [show m + (1 : ℤ) - 1 = m by omega]
  have hsourceMax : bankFiniteRootResponseMax (descendantsAtDepth Q j)
      M m (m + 40) (bankPartialInsertionWeights m 1 t) ω =
        ENNReal.ofReal (σ * lemmaVInverseDepthMax Q c j) := by
    exact bank_depth_max_physical Q M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω c hcoeff hEllCopen j
  have hQscale : Q ∈
      descendantsAtScale (originCube 2 (m + 40)) (m - 5) := by
    rw [hQ]
    exact Algsuperdiff.Section3.Provider.ErrorComparison.originCube_mem_descendantsAtScale
      (d := 2) (by omega)
  have hdist : Int.toNat ((originCube 2 (m + 40)).scale - (m - 5)) = 45 := by
    simp only [originCube]
    omega
  have hQdepth : Q ∈ descendantsAtDepth (originCube 2 (m + 40)) 45 := by
    rw [← hdist]
    rw [← descendantsAtScale_eq_descendantsAtDepth (originCube 2 (m + 40)) (by
      simp only [originCube]
      omega)]
    exact hQscale
  have hQroot : Q ∈ bankObserverRoots (originCube 2 (m + 40)) 5 := by
    rw [bankObserverRoots]
    rw [show (40 + 5 : ℕ) = 45 by norm_num]
    exact hQdepth
  let f : TriadicCube 2 → ℝ := fun R =>
    rootInverseResponse M R m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω
  have hsub (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) : R ∈ D := by
    unfold D bankObserverDepthRootUnion
    refine Finset.mem_biUnion.mpr ⟨5, by norm_num, ?_⟩
    have hQscaleValue : Q.scale = m - 5 := by
      rw [hQ]
      simp only [originCube]
    have hRscale := scale_eq_sub_of_mem_descendantsAtDepth hR
    have hRscaleMem : R ∈ descendantsAtScale Q R.scale := by
      have hscale : R.scale ≤ Q.scale := by rw [hRscale]; omega
      rw [descendantsAtScale_eq_descendantsAtDepth Q hscale]
      have hNat : Int.toNat (Q.scale - R.scale) = j := by
        rw [hRscale]
        rw [show Q.scale - (Q.scale - (j : ℤ)) = (j : ℤ) by omega]
        simp
      rw [hNat]
      exact hR
    have hRrootScale := mem_descendantsAtScale_trans hQscale hRscaleMem
    have hRdist : Int.toNat ((originCube 2 (m + 40)).scale - R.scale) = 45 + j := by
      rw [hRscale, hQscaleValue]
      simp only [originCube]
      rw [show (m + 40 : ℤ) - ((m - 5) - (j : ℤ)) = (45 : ℤ) + (j : ℤ) by omega]
      omega
    have hrootle : R.scale ≤ (originCube 2 (m + 40)).scale := by
      rw [hRscale, hQscaleValue]
      simp only [originCube]
      omega
    have hRdepthRoot : R ∈ descendantsAtDepth (originCube 2 (m + 40)) (45 + j) := by
      rw [← hRdist]
      rw [← descendantsAtScale_eq_descendantsAtDepth
        (originCube 2 (m + 40)) hrootle]
      exact hRrootScale
    rw [bankObserverDepthRoots]
    rw [show (40 + 5 : ℕ) = 45 by norm_num]
    exact hRdepthRoot
  have hDnonempty : D.Nonempty := by
    obtain ⟨R, hR⟩ := descendantsAtDepth_nonempty Q j
    exact ⟨R, hsub R hR⟩
  have hsourceSupEq : bankFiniteRootResponseMax (descendantsAtDepth Q j)
      M m (m + 40) (bankPartialInsertionWeights m 1 t) ω =
        ENNReal.ofReal (Book.Ch02.finsetSupReal (descendantsAtDepth Q j) f) := by
    simpa [f] using bank_response_max_eq_finsetSup
      (descendantsAtDepth Q j) (descendantsAtDepth_nonempty Q j)
        M m (m + 40) (bankPartialInsertionWeights m 1 t) ω
  have hglobalSupEq : bankFiniteRootResponseMax D M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω =
        ENNReal.ofReal (Book.Ch02.finsetSupReal D f) := by
    simpa [f] using bank_response_max_eq_finsetSup D hDnonempty
      M m (m + 40) (bankPartialInsertionWeights m 1 t) ω
  have hsup : Book.Ch02.finsetSupReal (descendantsAtDepth Q j) f ≤
      Book.Ch02.finsetSupReal D f := by
    apply Book.Ch02.finsetSupReal_le (descendantsAtDepth Q j)
      (descendantsAtDepth_nonempty Q j)
    intro R hR
    exact Algsuperdiff.Section3.Provider.ErrorComparison.le_finsetSupReal
      D f (hsub R hR)
  have hmax : bankFiniteRootResponseMax (descendantsAtDepth Q j)
      M m (m + 40) (bankPartialInsertionWeights m 1 t) ω ≤
        bankFiniteRootResponseMax D M m (m + 40)
          (bankPartialInsertionWeights m 1 t) ω := by
    rw [hsourceSupEq, hglobalSupEq]
    exact ENNReal.ofReal_le_ofReal hsup
  have hYlt : bankFiniteRootResponseMax D M m (m + 40)
      (bankPartialInsertionWeights m 1 t) ω < ⊤ := by
    rw [hglobalSupEq]
    exact ENNReal.ofReal_lt_top
  have hreal := ENNReal.toReal_mono hYlt.ne hmax
  have hphysical0 : 0 ≤ σ * lemmaVInverseDepthMax Q c j :=
    mul_nonneg hσ.le (lemmaVInverseDepthMax_nonneg Q c j)
  rw [hsourceMax, ENNReal.toReal_ofReal hphysical0] at hreal
  have hglobal : lemmaVInverseDepthMax Q a j ≤ Y := by
    rw [hlocalFrame]
    simpa [Y] using hreal
  have hsplit : Y ≤ inverseBankDepthA .localInverse M j +
      inverseBankDepthSlack M j + mixedOldLocalDepthRemainder M m t j ω := by
    dsimp [Y, mixedOldLocalDepthRemainder, inverseBankDepthBlockRemainder]
    exact (positive_split _ _ _).2
  have hprofile := (inverse_bank_depth_profile_bounds .localInverse M j).1
  have hbound : Y ≤ (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j +
      mixedOldLocalDepthRemainder M m t j ω := by
    calc
      Y ≤ inverseBankDepthA .localInverse M j + inverseBankDepthSlack M j +
          mixedOldLocalDepthRemainder M m t j ω := hsplit
      _ ≤ (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j +
          mixedOldLocalDepthRemainder M m t j ω := by
        nlinarith [hprofile]
  calc
    lemmaVInverseDepthMax Q a j ≤ Y := hglobal
    _ ≤ mixedOldDepthCoefficient M m t j ω := by
      simpa [Y, mixedOldDepthCoefficient] using hbound

private theorem old_theta_core_summable
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ω : Cutoff.CutoffSample 2) (Q : TriadicCube 2)
    (a : CoeffField 2)
    {lamA LamA : ℝ}
    (hEllA : IsEllipticFieldOn lamA LamA (openCubeSet Q) a)
    (htrace : ∀ j : ℕ,
      descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) =
        rawWeakTraceSequence M m Q t ω j)
    (hγ : M.gamma ≤ gammaZero) :
    Summable (fun j : ℕ => Scalar.inverseHistoryDiscount ^ (2 * j) *
      mixedOldDepthCoefficient M m t j ω *
        rawWeakTraceSequence M m Q t ω j) := by
  let α := Scalar.inverseHistoryDiscount
  let C : ℝ := 3683 / 2500
  let B : ℝ := mixedBridgeBstar M m t ω
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hT0 (j : ℕ) : 0 ≤ rawWeakTraceSequence M m Q t ω j :=
    raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j
  have hTsum : Summable (fun j : ℕ => α ^ j *
      rawWeakTraceSequence M m Q t ω j) := by
    have hs := old_signed_trace_depth_series_summable Q a hEllA
    apply hs.congr
    intro j
    rw [htrace j]
  have hB0 : 0 ≤ B := mixed_bridge_bstar_nonneg M m t ω
  have hR0 (j : ℕ) : 0 ≤ mixedOldLocalDepthRemainder M m t j ω := by
    change 0 ≤ positiveSplitRemainder _ _ _
    exact (positive_split _ _ _).1
  have hCformula (j : ℕ) :=
    mixed_old_depth_coefficient_formula M m t j ω
  have hC0 (j : ℕ) : 0 ≤ mixedOldDepthCoefficient M m t j ω := by
    rw [hCformula j]
    exact add_nonneg (mul_nonneg (by norm_num [C])
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)) (hR0 j)
  have hexp : -(1 / 4 : ℝ) + 2 * M.gamma < 0 := by
    dsimp [gammaZero] at hγ ⊢
    norm_num at hγ ⊢
    linarith
  have hq : α * (3 : ℝ) ^ (2 * M.gamma) < 1 := by
    have heq : α * (3 : ℝ) ^ (2 * M.gamma) =
        (3 : ℝ) ^ (-(1 / 4 : ℝ) + 2 * M.gamma) := by
      dsimp [α, Scalar.inverseHistoryDiscount]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    rw [heq]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
  have hbaseq : α ^ 2 * (3 : ℝ) ^ (2 * M.gamma) ≤ α := by
    have hmul : α ^ 2 * (3 : ℝ) ^ (2 * M.gamma) =
        α * (α * (3 : ℝ) ^ (2 * M.gamma)) := by ring
    rw [hmul]
    calc
      α * (α * (3 : ℝ) ^ (2 * M.gamma)) ≤ α * 1 :=
        mul_le_mul_of_nonneg_left hq.le hα0
      _ = α := by ring
  have hpow (j : ℕ) :
      α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) ≤ α ^ j := by
    have hpow3 : (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) =
        ((3 : ℝ) ^ (2 * M.gamma)) ^ j := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (2 * M.gamma)) j,
        Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      _ = (α ^ 2 * (3 : ℝ) ^ (2 * M.gamma)) ^ j := by
        rw [pow_mul, hpow3, ← mul_pow]
      _ ≤ α ^ j := pow_le_pow_left₀
        (mul_nonneg (sq_nonneg α)
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)) hbaseq j
  have hbaseline (j : ℕ) :
      α ^ (2 * j) * (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) ≤ C * α ^ j := by
    have hC : 0 ≤ C := by norm_num [C]
    calc
      _ = C * (α ^ (2 * j) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) := by ring
      _ ≤ C * α ^ j := mul_le_mul_of_nonneg_left (hpow j) hC
  have hRdiscount (j : ℕ) :
      α ^ (2 * j) * mixedOldLocalDepthRemainder M m t j ω ≤ B * α ^ j := by
    have hR := mixed_old_local_depth_remainder_discount_le_global M m t ht j ω
    calc
      _ = α ^ j * (α ^ j * mixedOldLocalDepthRemainder M m t j ω) := by
        rw [show 2 * j = j + j by omega, pow_add]
        ring
      _ ≤ α ^ j * B := mul_le_mul_of_nonneg_left hR (pow_nonneg hα0 j)
      _ = B * α ^ j := by ring
  have hmajorant : Summable (fun j : ℕ => (C + B) *
      (α ^ j * rawWeakTraceSequence M m Q t ω j)) :=
    hTsum.mul_left (C + B)
  apply Summable.of_nonneg_of_le
  · intro j
    exact mul_nonneg (mul_nonneg (pow_nonneg hα0 _) (hC0 j)) (hT0 j)
  · intro j
    have hcoef : α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω ≤
        (C + B) * α ^ j := by
      rw [hCformula j]
      calc
        α ^ (2 * j) *
            (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) +
              mixedOldLocalDepthRemainder M m t j ω) ≤
            C * α ^ j + B * α ^ j := by
          calc
            _ = α ^ (2 * j) *
                (C * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))) +
                  α ^ (2 * j) * mixedOldLocalDepthRemainder M m t j ω := by ring
            _ ≤ C * α ^ j + B * α ^ j := add_le_add (hbaseline j) (hRdiscount j)
        _ = (C + B) * α ^ j := by ring
    calc
      α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω *
          rawWeakTraceSequence M m Q t ω j ≤
        ((C + B) * α ^ j) * rawWeakTraceSequence M m Q t ω j :=
          mul_le_mul_of_nonneg_right hcoef (hT0 j)
      _ = (C + B) *
          (α ^ j * rawWeakTraceSequence M m Q t ω j) := by ring
  · exact hmajorant

/-- The actual directional source trace is paid pointwise by the local
OLD-Theta carrier on the same source cube and the same cutoff sample. The
source-state inputs are retained for the downstream IN-MIXED-BRIDGE consumer. -/
theorem main_source_bottom_pair_trace_le_local_old_theta
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ω : Cutoff.CutoffSample 2) :
    Main.mainSourceBottomPairTrace M m t ω ≤
      (1 + Scalar.inverseHistoryDiscount) *
        mixedOldTheta M m (originCube 2 (m - 5)) t ω := by
  classical
  have _hSourceGaussian : PlanarQ3Gaussian M h := hM
  have _hPast : nativeInductionState M h m := hpast m hm
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let α : ℝ := Scalar.inverseHistoryDiscount
  let σ : ℝ := Annealed.sigmaBar M m
  let a : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ
    (mainInsertionSkewCoefficient m t Q ω)
  let b : ℕ → ℝ := fun j => lemmaVInverseDepthMax Q a j
  let T : ℕ → ℝ := fun j => rawWeakTraceSequence M m Q t ω j
  let D : ℕ → ℝ := fun j => descendantsAverage Q j
    (fun R => traceDefect (openCubeSet R) a 1)
  have hσ : 0 < σ := by dsimp [σ]; exact (Annealed.sigmaBar_characterization M m).1
  have hfield (x : Vec 2) (hx : x ∈ openCubeSet Q) :
      a x = σ⁻¹ • (Model.partialInsertedCoefficient M m t ω).toFun x := by
    exact main_directional_response_frame_eq_scaled_partial_coefficient
      M m t Q ω x hx
  have hEllA := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) M.nu σ M.nu_pos hσ
      (mainInsertionSkewCoefficient m t Q ω)
  have htraceRaw (j : ℕ) :
      descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1) =
        rawWeakTraceSequence M m Q t ω j := by
    exact source_trace_average_eq M m t ht ω Q a hfield j
  have htrace (j : ℕ) : D j = T j := by
    simpa only [D, T] using htraceRaw j
  have hdepthCoeff (j : ℕ) : b j ≤ mixedOldDepthCoefficient M m t j ω := by
    dsimp [b, a, σ]
    exact directional_depth_max_le_global M m t ht ω Q rfl
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t Q ω))
      (responseFramePlanarCoefficientField_isElliptic
        (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m)
        M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (mainInsertionSkewCoefficient m t Q ω))
      (fun x hx => main_directional_response_frame_eq_scaled_partial_coefficient
        M m t Q ω x hx) j
  have hRaw : Main.mainSourceBottomPairTrace M m t ω ≤
      rawWeakTraceProxy b D := by
    simpa [Q, b, D, a, σ] using
      Main.main_source_bottom_pair_trace_raw_proxy M m t ω
  have hT0 (j : ℕ) : 0 ≤ T j := by
    exact raw_weak_trace_sequence_nonneg M m Q t ⟨ht.1, ht.2⟩ ω j
  have hα := Scalar.inverse_history_discount_range
  have hα0 : 0 ≤ α := hα.1.le
  have hpref : 0 ≤ 1 - α ^ 2 :=
    sub_nonneg.mpr (pow_le_one₀ hα0 hα.2.le)
  have hRawSummable : Summable (fun j : ℕ =>
      α ^ (2 * j) * b j * T j) := by
    have hs := old_signed_weak_trace_proxy_summable Q a hEllA
    apply hs.congr
    intro j
    simpa [α, b, T] using congrArg
      (fun z : ℝ => Scalar.inverseHistoryDiscount ^ (2 * j) *
        lemmaVInverseDepthMax Q a j * z) (htraceRaw j)
  have hThetaSummable := old_theta_core_summable M m t ht ω Q a hEllA
    htraceRaw hγ
  have hCoreLe (j : ℕ) :
      α ^ (2 * j) * b j * T j ≤
        α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω * T j := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hdepthCoeff j) (pow_nonneg hα0 _)) (hT0 j)
  have hsumCore : (∑' j : ℕ, α ^ (2 * j) * b j * T j) ≤
      ∑' j : ℕ, α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω * T j :=
    hRawSummable.tsum_le_tsum hCoreLe hThetaSummable
  have hRawEq : rawWeakTraceProxy b D =
      (1 - α ^ 2) * (∑' j : ℕ, α ^ (2 * j) * b j * T j) := by
    unfold rawWeakTraceProxy
    congr 1
    apply tsum_congr
    intro j
    dsimp [b]
    rw [htrace j]
  have hThetaEq : mixedOldTheta M m Q t ω =
      (1 - α ^ 2) *
        (∑' j : ℕ, α ^ (2 * j) *
          mixedOldDepthCoefficient M m t j ω * T j) := by
    unfold mixedOldTheta
    calc
      _ = ∑' j : ℕ, (1 - α ^ 2) *
          (α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω * T j) := by
        apply tsum_congr
        intro j
        simp [mixedOldThetaTerm, mixedDepthTraceAverage, T, α]
        ring
      _ = _ := tsum_mul_left
  have hProxyLeTheta : rawWeakTraceProxy b D ≤ mixedOldTheta M m Q t ω := by
    rw [hRawEq, hThetaEq]
    exact mul_le_mul_of_nonneg_left hsumCore hpref
  have hTheta0 : 0 ≤ mixedOldTheta M m Q t ω := by
    rw [hThetaEq]
    apply mul_nonneg hpref
    apply tsum_nonneg
    intro j
    change 0 ≤ α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω *
      rawWeakTraceSequence M m Q t ω j
    have hR0 : 0 ≤ mixedOldLocalDepthRemainder M m t j ω := by
      change 0 ≤ positiveSplitRemainder _ _ _
      exact (positive_split _ _ _).1
    have hC0 : 0 ≤ mixedOldDepthCoefficient M m t j ω := by
      rw [mixed_old_depth_coefficient_formula]
      exact add_nonneg (mul_nonneg (by norm_num)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)) hR0
    have hleft : 0 ≤ α ^ (2 * j) * mixedOldDepthCoefficient M m t j ω :=
      mul_nonneg (pow_nonneg hα0 _) hC0
    exact mul_nonneg hleft (hT0 j)
  have hfactor : 1 ≤ 1 + α := by linarith [hα.1]
  calc
    Main.mainSourceBottomPairTrace M m t ω ≤ rawWeakTraceProxy b D := hRaw
    _ ≤ mixedOldTheta M m Q t ω := hProxyLeTheta
    _ = 1 * mixedOldTheta M m Q t ω := by ring
    _ ≤ (1 + α) * mixedOldTheta M m Q t ω :=
      mul_le_mul_of_nonneg_right hfactor hTheta0

end
end ASDExplicitGamma.Inverse
