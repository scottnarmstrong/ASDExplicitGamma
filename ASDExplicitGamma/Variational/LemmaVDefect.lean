module

public import ASDExplicitGamma.Variational.TraceDefect
public import Homogenization.CoarseGraining.MuRecoveryBlockResponse

/-! Lemma V (A): primal/adjoint harmonic defect energies of each load. -/

@[expose] public section

namespace ASDExplicitGamma.Variational

open Homogenization MeasureTheory

noncomputable section

/-- Each doubled minimum splits into primal and adjoint harmonic energies.
The half-pair convention of CoarseGraining identifies its two harmonic
functions with `u₊` and `u₋` in Lemma V. -/
theorem lemmaV_load_defect_decomposition {d : ℕ} [NeZero d]
    {m : ℤ} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) a)
    (P : BlockVec d) :
    ∃ u : AHarmonicFunction a (openCubeSet (originCube d m)),
      ∃ v : AHarmonicFunction (adjointCoeffField a) (openCubeSet (originCube d m)),
        2 * Mu (openCubeSet (originCube d m)) P a - 2 * vecDot P.1 P.2 =
          volumeAverage (openCubeSet (originCube d m))
            (scalarVariationEnergyIntegrand (adjointCoeffField a) v) ∧
        2 * Mu (openCubeSet (originCube d m)) P a + 2 * vecDot P.1 P.2 =
          volumeAverage (openCubeSet (originCube d m))
            (scalarVariationEnergyIntegrand a u) := by
  obtain ⟨R, hEllR, hCompat⟩ :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := lam) (Lam := Lam) m a hEll
  let system := R.toMuOperatorSystemDataOfIsEllipticFieldOn hEllR
    (volume_openCubeSet_originCube_toReal_pos (d := d) m)
  let recovery := R.toMuCorrectionSpaceRecoveryData
  obtain ⟨u, v, hpair⟩ :=
    recovery.exists_blockResponsePairHalfState_ae_eq_recoveredField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system (isOpenBoundedConvexDomain_openCubeSet (originCube d m)) hEll
      (volume_openCubeSet_originCube_toReal_pos (d := d) m).ne' P
  have henergy : blockEnergyAverage (openCubeSet (originCube d m)) a
      (blockResponsePairHalfState a u v) = Mu (openCubeSet (originCube d m)) P a := by
    rw [← recovery.recoveredField_blockEnergyAverage_eq_mu system hCompat.mu_eq_muCandidate P]
    unfold blockEnergyAverage volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hpair] with x hx
    exact congrArg (fun z => (1 / 2 : ℝ) *
      blockVecDot z (blockMatVecMul (blockCoeffField a x) z)) hx
  have hpairing : volumeAverage (openCubeSet (originCube d m))
      (fun x => vecDot ((blockResponsePairHalfState a u v).potential x)
        ((blockResponsePairHalfState a u v).flux x)) = vecDot P.1 P.2 := by
    rw [← recovery.recoveredField_average_pairing_openCubeSet_originCube system P]
    unfold volumeAverage
    congr 1
    apply integral_congr_ae
    filter_upwards [hpair] with x hx
    exact congrArg (fun z : BlockVec d => vecDot z.1 z.2) hx
  have hsplit :=
    blockEnergyAverage_blockResponsePairHalfState_eq_quarter_scalarVariationEnergySum_of_isEllipticFieldOn
      a (measurableSet_openCubeSet _) hEll u v
  have hdiff :=
    volumeAverage_statePairing_blockResponsePairHalfState_eq_quarter_scalarVariationEnergy_sub
      a hEll u v
  refine ⟨u, v, ?_, ?_⟩ <;> linarith only [henergy, hpairing, hsplit, hdiff]

/-- The normalized plus and minus loads have pairing `±1/2`. -/
theorem lemmaV_orthonormalFrameLoad_pairing (i : Fin 2) (ε : ℝ) :
    2 * vecDot (orthonormalFrameLoad i ε).1 (orthonormalFrameLoad i ε).2 = ε := by
  have hs : ((Real.sqrt 2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  fin_cases i <;>
    simp [orthonormalFrameLoad, blockBasis, vecDot, Fin.sum_univ_two]
  all_goals
    calc
      2 * ((Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹ * ε)) =
          2 * ((Real.sqrt 2)⁻¹ ^ 2) * ε := by ring
      _ = ε := by rw [hs]; ring

/-- The four-load sum of `E_P − 1` is exactly the frozen trace defect in
frame one. Apply this to the coefficient already divided by its frame. -/
theorem lemmaV_traceDefect_eq_sum_load_defects {m : ℤ} {a : CoeffField 2}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube 2 m)) a) :
    traceDefect (cubeSet (originCube 2 m)) a 1 =
      ∑ i : Fin 2,
        ((2 * Mu (cubeSet (originCube 2 m)) (orthonormalFrameLoad i 1) a - 1) +
          (2 * Mu (cubeSet (originCube 2 m)) (orthonormalFrameLoad i (-1)) a - 1)) := by
  have hload (i : Fin 2) (ε : ℝ) (hε : ε ^ 2 = 1) :
      2 * Mu (cubeSet (originCube 2 m)) (orthonormalFrameLoad i ε) a =
        ((coarseBlockMatrix (cubeSet (originCube 2 m)) a).upperLeft i i +
          (coarseBlockMatrix (cubeSet (originCube 2 m)) a).lowerRight i i +
          ε * ((coarseBlockMatrix (cubeSet (originCube 2 m)) a).upperRight i i +
            (coarseBlockMatrix (cubeSet (originCube 2 m)) a).lowerLeft i i)) / 2 := by
    rw [mu_eq_half_coarseBlockMatrix_elliptic_triCube hlam hEll]
    have h := orthonormalFrameLoad_energy
      (coarseBlockMatrix (cubeSet (originCube 2 m)) a) 1 i ε hε
    simpa [frameMatrix] using h
  simp_rw [hload _ 1 (by norm_num), hload _ (-1) (by norm_num)]
  simp [traceDefect, Matrix.trace, Fin.sum_univ_two]
  ring

/-- Lemma V (A), on a planar cube: the frozen normalized trace defect is
the sum of the adjoint defect energies on the plus loads and the primal
defect energies on the minus loads. No harmonicity or defect identity is
assumed: the witnesses come from the variational minimum. -/
theorem lemmaV_trace_defect_decomposition {m : ℤ} {a : CoeffField 2}
    {lam Lam : ℝ} (hlam : 0 < lam)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube 2 m)) a) :
    ∃ u : Fin 2 → AHarmonicFunction a (openCubeSet (originCube 2 m)),
      ∃ v : Fin 2 → AHarmonicFunction (adjointCoeffField a) (openCubeSet (originCube 2 m)),
        (∀ i, 2 * Mu (cubeSet (originCube 2 m)) (orthonormalFrameLoad i 1) a - 1 =
          volumeAverage (openCubeSet (originCube 2 m))
            (scalarVariationEnergyIntegrand (adjointCoeffField a) (v i))) ∧
        (∀ i, 2 * Mu (cubeSet (originCube 2 m)) (orthonormalFrameLoad i (-1)) a - 1 =
          volumeAverage (openCubeSet (originCube 2 m))
            (scalarVariationEnergyIntegrand a (u i))) ∧
        traceDefect (cubeSet (originCube 2 m)) a 1 =
          ∑ i : Fin 2,
            (volumeAverage (openCubeSet (originCube 2 m))
                (scalarVariationEnergyIntegrand (adjointCoeffField a) (v i)) +
              volumeAverage (openCubeSet (originCube 2 m))
                (scalarVariationEnergyIntegrand a (u i))) := by
  classical
  have hEllO := hEll.mono (measurableSet_openCubeSet (originCube 2 m))
    (openCubeSet_subset_cubeSet (originCube 2 m))
  choose up vp hp using fun i : Fin 2 =>
    lemmaV_load_defect_decomposition hEllO (orthonormalFrameLoad i 1)
  choose um vm hm using fun i : Fin 2 =>
    lemmaV_load_defect_decomposition hEllO (orthonormalFrameLoad i (-1))
  have hp' (i : Fin 2) :
      2 * Mu (cubeSet (originCube 2 m)) (orthonormalFrameLoad i 1) a - 1 =
        volumeAverage (openCubeSet (originCube 2 m))
          (scalarVariationEnergyIntegrand (adjointCoeffField a) (vp i)) := by
    rw [Mu_cubeSet_originCube_eq_openCubeSet]
    simpa only [lemmaV_orthonormalFrameLoad_pairing, mul_assoc] using (hp i).1
  have hm' (i : Fin 2) :
      2 * Mu (cubeSet (originCube 2 m)) (orthonormalFrameLoad i (-1)) a - 1 =
        volumeAverage (openCubeSet (originCube 2 m))
          (scalarVariationEnergyIntegrand a (um i)) := by
    rw [Mu_cubeSet_originCube_eq_openCubeSet]
    have h := (hm i).2
    rw [lemmaV_orthonormalFrameLoad_pairing] at h
    simpa only [sub_eq_add_neg] using h
  refine ⟨um, vp, hp', hm', ?_⟩
  rw [lemmaV_traceDefect_eq_sum_load_defects hlam hEll]
  exact Finset.sum_congr rfl fun i _ => by rw [hp', hm']

end

end ASDExplicitGamma.Variational
