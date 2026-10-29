/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.CirFiniteEvenHistoryProfile
public import ASDExplicitGamma.AllOrder.CirResetTrace

/-! # Pointwise bridge from actual CIR inverses to reset depth maxima -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Model ASDExplicitGamma.Response
  ASDExplicitGamma.Variational
open Homogenization.Book

namespace ASDExplicitGamma.AllOrder

/-- The actual bounded-continuous response restriction on one square along a
completed-shell insertion path. -/
noncomputable def aoCirInsertedResponseCoefficient
    (Q : TriadicCube 2) (n : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (N : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    ResponseCoefficient (openCubeSet Q) :=
  cirSquareRestrictionCLM Q hQ
    (modelInsertedScalar (closure (cubeSet (originCube 2 n))) (N - 1) t ω)

/-- The finite descendant maxima in the complete CIR inverse history are the
same as the reset maxima on the actual one-shell insertion path. -/
theorem aoCir_step_inverse_depth_max_eq_lemmaV
    (M : ABKModel 2) (Q : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (N : ℤ) (hN : Q.scale ≤ N) (q t : ℝ) (d : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    aoCirResetInverseDepthMax M Q d N Q.scale q t ω =
      lemmaVInverseDepthMax Q
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M Q.scale : ℝ)
          (aoCirInsertedResponseCoefficient Q n hQ N t ω)) d := by
  let K := closure (cubeSet (originCube 2 n))
  let kQ : ResponseCoefficient (openCubeSet Q) :=
    aoCirInsertedResponseCoefficient Q n hQ N t ω
  let a : CoeffField 2 := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M Q.scale : ℝ) kQ
  let σ : ℝ := Annealed.sigmaBar M Q.scale
  let lam : ℝ := M.nu / σ
  let Lam : ℝ := (lam ^ 2 + (‖kQ‖ / σ) ^ 2) / lam
  have hσ : 0 < (Annealed.sigmaBar M Q.scale : ℝ) :=
    (Annealed.sigmaBar_characterization M Q.scale).1
  have hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a := by
    simpa only [a, kQ, aoCirInsertedResponseCoefficient, σ, lam, Lam] using
      lemmaV_frameCoefficient_isEllipticOn
      (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M Q.scale)
      M.nu_pos hσ kQ
  change Book.Ch02.finsetSupReal (descendantsAtDepth Q d)
      (fun R => rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand q)) N Q.scale
        (aoCirStepWeights N t) ω) =
    Book.Ch02.finsetSupReal (descendantsAtDepth Q d)
      (fun R => Book.Ch02.matrixNorm
        (sigmaStarInvCoarse (openCubeSet R) a))
  apply Book.Ch02.finsetSupReal_congr
  intro R hR
  have hRQ : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hRK : closure (openCubeSet R) ⊆ K :=
    (closure_mono hRQ).trans hQ
  let kR : ResponseCoefficient (openCubeSet R) :=
    cirSquareRestrictionCLM R hRK (modelInsertedScalar K (N - 1) t ω)
  have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (measurableSet_openCubeSet R) hRQ
  have hAEopen : responseFramePlanarCoefficientField M.nu
      (Annealed.sigmaBar M Q.scale : ℝ) kR =ᵐ[
        volume.restrict (openCubeSet R)] a := by
    filter_upwards [ae_restrict_mem (μ := volume)
      (measurableSet_openCubeSet R)] with x hxR
    have hxQ : x ∈ openCubeSet Q := hRQ hxR
    have hExt : responseCoefficientExtension kR x =
        responseCoefficientExtension kQ x := by
      rw [responseCoefficientExtension_eq kR hxR,
        responseCoefficientExtension_eq kQ hxQ]
      change modelInsertedScalar K (N - 1) t ω ⟨x, hRK (subset_closure hxR)⟩ =
        modelInsertedScalar K (N - 1) t ω ⟨x, hQ (subset_closure hxQ)⟩
      congr 1
    change responsePlanarCoefficient (M.nu /
      (Annealed.sigmaBar M Q.scale : ℝ))
        (responseCoefficientExtension kR x /
          (Annealed.sigmaBar M Q.scale : ℝ)) = _
    rw [hExt]
    rfl
  have hAE : responseFramePlanarCoefficientField M.nu
      (Annealed.sigmaBar M Q.scale : ℝ) kR =ᵐ[
        volume.restrict (cubeSet R)] a := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
    exact hAEopen
  have hcoarse : coarseBlockMatrix (cubeSet R)
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M Q.scale : ℝ) kR) =
      coarseBlockMatrix (cubeSet R) a := coarseBlockMatrix_congr_of_ae_eq hAE
  have hmN : protectedOldLabel R.scale (orderBand q) < N := by
    have hscale := scale_eq_sub_of_mem_descendantsAtDepth hR
    simp only [protectedOldLabel]
    omega
  have hroot := aoCir_step_inverse_eq_responseFrame_norm M R n ell hRK hK
    (protectedOldLabel R.scale (orderBand q)) N Q.scale hmN t ω
  have hroot' : rootInverseObservable M R
      (protectedOldLabel R.scale (orderBand q)) N Q.scale
      (aoCirStepWeights N t) ω =
      Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R) a) := by
    have hroot'' : rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand q)) N Q.scale
        (aoCirStepWeights N t) ω =
        Book.Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a).lowerRight := by
      rw [hcoarse] at hroot
      exact hroot
    calc
      _ = Book.Ch02.matrixNorm
          (coarseBlockMatrix (cubeSet R) a).lowerRight := hroot''
      _ = _ := congrArg Book.Ch02.matrixNorm
        (ASDExplicitGamma.Scalar.inverse_history_lowerRight R a hEllR).symm
  exact hroot'

/-- The pointwise inverse-root observable on a descendant is the lower-right
inverse norm computed from the parent response coefficient. This is the
cellwise form of `aoCir_step_inverse_depth_max_eq_lemmaV`, exposed for
measurability of finite histories built from nested descendant families. -/
theorem aoCir_step_inverse_cell_eq_responseFrame_norm
    (M : ABKModel 2) (Q R : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (N : ℤ) (hN : Q.scale ≤ N) (q t : ℝ) (d : ℕ)
    (hR : R ∈ descendantsAtDepth Q d) (ω : Cutoff.CutoffSample 2) :
    rootInverseObservable M R
      (protectedOldLabel R.scale (orderBand q)) N Q.scale
      (aoCirStepWeights N t) ω =
    Book.Ch02.matrixNorm (sigmaStarInvCoarse (openCubeSet R)
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M Q.scale : ℝ)
        (aoCirInsertedResponseCoefficient Q n hQ N t ω))) := by
  let K := closure (cubeSet (originCube 2 n))
  let kQ := aoCirInsertedResponseCoefficient Q n hQ N t ω
  let a := responseFramePlanarCoefficientField M.nu
    (Annealed.sigmaBar M Q.scale : ℝ) kQ
  let σ := (Annealed.sigmaBar M Q.scale : ℝ)
  let lam := M.nu / σ
  let Lam := (lam ^ 2 + (‖kQ‖ / σ) ^ 2) / lam
  have hσ : 0 < (Annealed.sigmaBar M Q.scale : ℝ) :=
    (Annealed.sigmaBar_characterization M Q.scale).1
  have hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a := by
    simpa only [a, kQ, aoCirInsertedResponseCoefficient, σ, lam, Lam] using
      lemmaV_frameCoefficient_isEllipticOn
        (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M Q.scale)
        M.nu_pos hσ kQ
  have hRQ : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR
  have hRK : closure (openCubeSet R) ⊆ K := (closure_mono hRQ).trans hQ
  let kR : ResponseCoefficient (openCubeSet R) :=
    cirSquareRestrictionCLM R hRK (modelInsertedScalar K (N - 1) t ω)
  have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (measurableSet_openCubeSet R) hRQ
  have hAEopen : responseFramePlanarCoefficientField M.nu σ kR =ᵐ[
      volume.restrict (openCubeSet R)] a := by
    filter_upwards [ae_restrict_mem (μ := volume)
      (measurableSet_openCubeSet R)] with x hxR
    have hxQ : x ∈ openCubeSet Q := hRQ hxR
    have hExt : responseCoefficientExtension kR x =
        responseCoefficientExtension kQ x := by
      rw [responseCoefficientExtension_eq kR hxR,
        responseCoefficientExtension_eq kQ hxQ]
      change modelInsertedScalar K (N - 1) t ω ⟨x, hRK (subset_closure hxR)⟩ =
        modelInsertedScalar K (N - 1) t ω ⟨x, hQ (subset_closure hxQ)⟩
      congr 1
    change responsePlanarCoefficient (M.nu / σ)
      (responseCoefficientExtension kR x / σ) = _
    rw [hExt]
    rfl
  have hAE : responseFramePlanarCoefficientField M.nu σ kR =ᵐ[
      volume.restrict (cubeSet R)] a := by
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet R]
    exact hAEopen
  have hcoarse : coarseBlockMatrix (cubeSet R)
      (responseFramePlanarCoefficientField M.nu σ kR) =
      coarseBlockMatrix (cubeSet R) a := coarseBlockMatrix_congr_of_ae_eq hAE
  have hmN : protectedOldLabel R.scale (orderBand q) < N := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth hR
    simp only [protectedOldLabel]
    omega
  have hroot := aoCir_step_inverse_eq_responseFrame_norm M R n ell hRK hK
    (protectedOldLabel R.scale (orderBand q)) N Q.scale hmN t ω
  have hroot' : rootInverseObservable M R
      (protectedOldLabel R.scale (orderBand q)) N Q.scale
      (aoCirStepWeights N t) ω =
      Book.Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a).lowerRight := by
    have hroot'' : rootInverseObservable M R
        (protectedOldLabel R.scale (orderBand q)) N Q.scale
        (aoCirStepWeights N t) ω =
        Book.Ch02.matrixNorm
          (coarseBlockMatrix (cubeSet R) a).lowerRight := by
      rw [hcoarse] at hroot
      exact hroot
    exact hroot''
  calc
    _ = Book.Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a).lowerRight := hroot'
    _ = _ := congrArg Book.Ch02.matrixNorm
      (ASDExplicitGamma.Scalar.inverse_history_lowerRight R a hEllR).symm

/-- The reset-series value does not depend on the order parameter used to
choose protected labels: every depth maximum is the same Lemma V maximum. -/
theorem aoCir_reset_inverse_depth_profile_series_order_independent
    (M : ABKModel 2) (Q : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (N : ℤ) (hN : Q.scale ≤ N) (j : ℕ)
    (q₁ q₂ t : ℝ) (ω : Cutoff.CutoffSample 2) :
    aoCirResetInverseDepthProfileSeries M Q j N q₁ t ω =
      aoCirResetInverseDepthProfileSeries M Q j N q₂ t ω := by
  unfold aoCirResetInverseDepthProfileSeries
  apply congrArg (fun x : ℝ => (1 - aoCirInverseHistoryDiscount) * x)
  apply tsum_congr
  intro d
  apply congrArg (fun x : ℝ => aoCirInverseHistoryDiscount ^ d * x)
  calc
    aoCirResetInverseDepthMax M Q (j + d) N Q.scale q₁ t ω =
        lemmaVInverseDepthMax Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M Q.scale : ℝ)
            (aoCirInsertedResponseCoefficient Q n hQ N t ω)) (j + d) :=
      aoCir_step_inverse_depth_max_eq_lemmaV M Q n ell hQ hK N hN q₁ t (j + d) ω
    _ = aoCirResetInverseDepthMax M Q (j + d) N Q.scale q₂ t ω :=
      (aoCir_step_inverse_depth_max_eq_lemmaV M Q n ell hQ hK N hN q₂ t (j + d) ω).symm

/-- A fixed-order measurable envelope controls the tile history at every
profile order. -/
theorem aoCir_step_tile_history_le_fixed_reset_profile_series
    (M : ABKModel 2) (Q : TriadicCube 2) (n ell : ℤ)
    (hQ : closure (openCubeSet Q) ⊆ closure (cubeSet (originCube 2 n)))
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (N : ℤ) (hN : Q.scale ≤ N) (j : ℕ) (q t : ℝ)
    (ω : Cutoff.CutoffSample 2) :
    pureFluxSourceTileHistory Q j
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M Q.scale : ℝ)
          (aoCirInsertedResponseCoefficient Q n hQ N t ω)) ≤
      aoCirResetInverseDepthProfileSeries M Q j N 48 t ω := by
  let kQ := aoCirInsertedResponseCoefficient Q n hQ N t ω
  let σ : ℝ := Annealed.sigmaBar M Q.scale
  let a : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ kQ
  let lam : ℝ := M.nu / σ
  let Lam : ℝ := (lam ^ 2 + (‖kQ‖ / σ) ^ 2) / lam
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M Q.scale).1
  have hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a := by
    simpa only [a, kQ, aoCirInsertedResponseCoefficient, σ, lam, Lam] using
      lemmaV_frameCoefficient_isEllipticOn
        (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M Q.scale)
        M.nu_pos hσ kQ
  have hseries (q' : ℝ) :
      (1 - aoCirInverseHistoryDiscount) *
        ∑' d : ℕ, aoCirInverseHistoryDiscount ^ d *
          lemmaVInverseDepthMax Q a (j + d) =
      aoCirResetInverseDepthProfileSeries M Q j N q' t ω := by
    unfold aoCirResetInverseDepthProfileSeries
    apply congrArg (fun x : ℝ => (1 - aoCirInverseHistoryDiscount) * x)
    apply tsum_congr
    intro d
    have hdepth := aoCir_step_inverse_depth_max_eq_lemmaV M Q n ell
      hQ hK N hN q' t (j + d) ω
    apply congrArg (fun x : ℝ => aoCirInverseHistoryDiscount ^ d * x)
    simpa only [a, kQ, σ] using hdepth.symm
  calc
    _ ≤ (1 - aoCirInverseHistoryDiscount) *
        ∑' d : ℕ, aoCirInverseHistoryDiscount ^ d *
          lemmaVInverseDepthMax Q a (j + d) :=
      pureFlux_source_tile_history_le_combined_depth_series Q j a hEll
    _ = aoCirResetInverseDepthProfileSeries M Q j N q t ω := hseries q
    _ = aoCirResetInverseDepthProfileSeries M Q j N 48 t ω :=
      aoCir_reset_inverse_depth_profile_series_order_independent
        M Q n ell hQ hK N hN j q 48 t ω

end ASDExplicitGamma.AllOrder
