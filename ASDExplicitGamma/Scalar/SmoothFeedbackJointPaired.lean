/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackJointFeedback
public import ASDExplicitGamma.Scalar.OldHessianTrialPairedWeak
public import ASDExplicitGamma.Native.OldSignedCellHistories
public import ASDExplicitGamma.Native.OldSignedResidualReciprocalEnergy

/-! Paired weak-Haar charge of the actual OLD cell residual. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section
/-- A field and its coefficient-reflected field, both compatible in the
literal scalar spaces, form a block response. The two Hodge equations give
the response orthogonality against the two components of every block test. -/
theorem smooth_feedback_response_of_primal_dual_compatible
    (U : Set (Vec 2)) (a : CoeffField 2) (Y : Vec 2 → BlockVec 2)
    (hY : ScalarCompatible U Y)
    (hdual : ScalarCompatible U (fun x =>
      (blockMatVecMul (blockCoeffField a x) (Y x)).swap)) :
    BlockResponseSpace a U
      ⟨fun x => (Y x).1, fun x => (Y x).2⟩ := by
  classical
  refine ⟨hY.2.1, hY.2.2, ?_⟩
  intro T hT
  let upper : Vec 2 → Vec 2 := fun x =>
    (blockMatVecMul (blockCoeffField a x) (Y x)).1
  let lower : Vec 2 → Vec 2 := fun x =>
    (blockMatVecMul (blockCoeffField a x) (Y x)).2
  have hUpperSol : IsSolenoidalOn U upper := by
    change IsSolenoidalOn U upper
    simpa [upper] using hdual.2.2
  have hLowerPot : IsPotentialOn U lower := by
    change IsPotentialOn U lower
    simpa [lower] using hdual.2.1
  have hUpperMem : MemVectorL2 U upper := by
    simpa [upper] using memVectorL2_snd_of_memBlockL2 hdual.1
  obtain ⟨φ₀, hφ₀⟩ := hT.1
  have hTestPotMem : MemVectorL2 U T.potential := by
    rw [← hφ₀]
    exact φ₀.toH1Function.grad_memVectorL2
  let f₁ : Vec 2 → ℝ := fun x =>
    vecDot (T.potential x) (upper x)
  let f₂ : Vec 2 → ℝ := fun x =>
    vecDot (T.flux x) (lower x)
  have hf₁ : IntegrableOn f₁ U := by
    exact integrableOn_vecDot_of_memVectorL2 hTestPotMem hUpperMem
  have hf₁zero : ∫ x in U, f₁ x ∂volume = 0 := by
    have h := hUpperSol φ₀
    simpa [f₁, hφ₀, vecDot_comm] using h
  have hf₂zero : ∫ x in U, f₂ x ∂volume = 0 := by
    obtain ⟨ψ, hψ⟩ := hLowerPot
    have h := hT.2 ψ
    simpa [f₂, hψ] using h
  have hsplit : (fun x => blockVecDot (T.eval x)
      (blockMatVecMul (blockCoeffField a x) (Y x))) =
      (fun x => f₁ x + f₂ x) := by
    funext x
    simp [f₁, f₂, blockVecDot, BlockState.eval, upper, lower]
  change ∫ x in U, blockVecDot (T.eval x)
      (blockMatVecMul (blockCoeffField a x) (Y x)) ∂volume = 0
  rw [hsplit]
  by_cases hf₂ : IntegrableOn f₂ U
  · rw [integral_add hf₁ hf₂, hf₁zero, hf₂zero, add_zero]
  · have hnotSum : ¬ IntegrableOn (fun x => f₁ x + f₂ x) U := by
      intro hsum
      apply hf₂
      have hdiff := hsum.sub hf₁
      convert hdiff using 1
      ext x
      change f₂ x = f₁ x + f₂ x - f₁ x
      rw [add_sub_cancel_left]
    rw [integral_undef hnotSum]

/-- A compatible actual cell source residual has its first and reciprocal
weak-Haar energies controlled together by one exact local inverse history. -/
theorem smooth_feedback_old_cell_residual_paired_weak_energy_of_compatible
    (Q R : TriadicCube 2) (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (F : Vec 2 → BlockVec 2) (hF : MemBlockL2 (openCubeSet Q) F)
    (hCompat : ScalarCompatible (openCubeSet Q) F) :
    let kR := oldSignedCellCoefficient Q R hRQ k
    let aR := responseFramePlanarCoefficientField nu sigma kR
    let Y := oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF
    vectorWeakHaarEnergy R (fun x i => (Y x).1 i) +
      vectorWeakHaarEnergy R (fun x =>
        (scalarCoefficientFlux aR Y x).2) ≤
      lemmaVInverseHistory R aR ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        oldSignedEnergyPairing R nu sigma kR Y Y := by
  classical
  dsimp only
  let kR := oldSignedCellCoefficient Q R hRQ k
  let aR := responseFramePlanarCoefficientField nu sigma kR
  let Y : BlockL2 (openCubeSet R) :=
    oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k F hF
  have hYmem : MemBlockL2 (openCubeSet R) Y := Y.property
  let hFR : MemBlockL2 (openCubeSet R) F :=
    hF.mono_measure (Measure.restrict_mono_set volume hRQ)
  have hRemoved := old_signed_cell_removed_variation Q R hRQ
    nu sigma hnu hsigma k F hF
  have hCorrection : ScalarCompatible (openCubeSet R) (fun x => F x - Y x) :=
    scalar_variation_compatible hRemoved
  have hFcell : ScalarCompatible (openCubeSet R) F :=
    old_signed_compatible_restrict Q R hRQ hCompat
  have hYcompat : ScalarCompatible (openCubeSet R) Y := by
    have hsub := old_signed_compatible_sub hFcell hCorrection
    change ScalarCompatible (openCubeSet R)
      (fun x => F x - (F x - Y x)) at hsub
    simpa only [sub_sub_cancel] using hsub
  have hdual : ScalarCompatible (openCubeSet R) (fun x =>
      (blockMatVecMul (blockCoeffField aR x) (Y x)).swap) := by
    change ScalarCompatible (openCubeSet R)
      (oldSignedDualReflection R nu sigma kR Y)
    simpa [oldSignedDualReflection, oldSignedCellResidual, aR, kR, Y] using
        old_signed_reflected_residual_compatible R nu sigma hnu hsigma kR
          (toHilbertBlockL2OfBlockField hFR)
  let W : BlockState 2 := ⟨fun x => (Y x).1, fun x => (Y x).2⟩
  have hW : BlockResponseSpace aR (openCubeSet R) W := by
    simpa [W] using
      smooth_feedback_response_of_primal_dual_compatible
        (openCubeSet R) aR Y hYcompat hdual
  have hWmem : MemBlockL2 (openCubeSet R) W.eval := by
    change MemBlockL2 (openCubeSet R)
      (fun x => ((Y x).1, (Y x).2))
    have hYeta : (fun x => ((Y x).1, (Y x).2)) = Y := by
      funext x
      exact Prod.eta (Y x)
    rw [hYeta]
    exact hYmem
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet R) nu sigma hnu hsigma kR
  have hpaired := old_hessian_paired_response_weak R hEll W hW hWmem
  have hpair : blockPairingAverage (openCubeSet R) aR W W =
      oldSignedEnergyPairing R nu sigma kR Y Y := by
    change volumeAverage (openCubeSet R) (fun x =>
      blockVecDot (W.eval x)
        (blockMatVecMul (blockCoeffField aR x) (W.eval x))) =
      volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (Y x)
          (blockMatVecMul (blockCoeffField aR x) (Y x)))
    congr 1
  calc
    _ ≤ lemmaVInverseHistory R aR ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          blockPairingAverage (openCubeSet R) aR W W := by
      simpa [W, BlockState.eval, scalarCoefficientFlux, Y, aR, kR] using hpaired
    _ = lemmaVInverseHistory R aR ((3 : ℝ) ^ (1 / 4 : ℝ)) *
          oldSignedEnergyPairing R nu sigma kR Y Y := by rw [hpair]

end

end ASDExplicitGamma.Scalar
