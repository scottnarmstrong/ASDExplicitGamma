module

public import ASDExplicitGamma.Native.ParentHistoryDiscounted
public import ASDExplicitGamma.Native.ParentHistoryRootBound
public import ASDExplicitGamma.Native.ParentHistoryFiniteness

/-! Sharp actual-law physical-history restoration with the original rare reserve. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Restore the complete discounted physical history in the actual true
frame. The common-center, original bank and every depth are retained;
all norm, finiteness and rare-payment estimates are proved internally. -/
theorem parent_history_physical_restore
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (P : TriadicCube 2) (n : ℤ)
    (r : ℕ) (hr : r ≤ 5) (hP : P.scale=n-(r:ℤ))
    (height : ℕ) (_hheight : 1 ≤ height)
    (hpast : ∀ k<n,nativeInductionState M h k)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    eLpNorm (parentBoundaryBandMaxTraceHistory M n height P t) 2
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
      ((Real.sqrt ((eLpNorm (parentBoundaryCommonCenteredMaxHistory M P n height t)
          20 (Cutoff.cutoffSampleLaw M).toMeasure).toReal)+
        Real.sqrt (2*t*parentBoundaryCommonBandVariance M h n height)*
          ((3:ℝ)^((1:ℝ)/4)*Real.sqrt (3683/2500:ℝ)+
            (105:ℝ)^((1:ℝ)/8)*Real.sqrt (3/10^46:ℝ)))^2) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X := fun ω => (parentBoundaryBandMaxTraceHistory M n height P t ω).toReal
  let C := fun ω => (parentBoundaryCommonCenteredMaxHistory M P n height t ω).toReal
  let G := fun ω => parentBoundaryCommonCubeCenterValue P n height t ω/(Annealed.sigmaBar M n:ℝ)
  let B := parentBoundaryCommonSingletonHistory M P n n height t
  let R := inverseBankPopulationRemainder .localInverse ({P}:Finset (TriadicCube 2)) M n
    (n+(height:ℤ)) (parentBoundaryObserverBandWeights n t)
  let V := parentBoundaryCommonBandVariance M h n height
  let g4 := (3:ℝ)^((1:ℝ)/4)*Real.sqrt (t*V)
  let g8 := (105:ℝ)^((1:ℝ)/8)*Real.sqrt (t*V)
  have hC := parent_history_centered_memLp M h hM hg P n r hP height hpast t ht1
  have hG8 : MemLp G 8 μ := parent_boundary_common_cube_center_memLp M h hM P n height t 8 (by finiteness)
  have hrare := parent_common_singleton_history_rare_inputs M h hM hg P n r hr hP height hpast t ht1
  have hRcap : eLpNorm R 128 μ ≤ ENNReal.ofReal (3/10^46:ℝ) := hrare.2.1
  have hR128 : MemLp R 128 μ := hRcap.trans_lt ENNReal.ofReal_lt_top
  have hbank := parent_boundary_common_singleton_bank M h hM hg P n n
    (by rw [hP]; omega) (by rw [hP]; omega) le_rfl height hpast t ht1
  have hR0 (ω) : 0 ≤ R ω := hbank.remainder_nonneg ω
  have hG4cap : eLpNorm G 4 μ ≤ ENNReal.ofReal g4 :=
    parent_common_center_L4_bound M h hM P n height t ht0 ht1
  have hG8cap : eLpNorm G 8 μ ≤ ENNReal.ofReal g8 :=
    parent_common_center_L8_bound M h hM P n height t ht0 ht1
  have hrestore := parent_history_sqrt_restore_ae M h hM hg P n r hr hP height hpast t ht1
  have hXsm : AEStronglyMeasurable X μ :=
    (parent_boundary_band_extended_max_trace_measurable M n height P t).ennreal_toReal.aestronglyMeasurable
  have hpay := parent_history_root_payment μ X C G B R hXsm
    (fun _ => ENNReal.toReal_nonneg) hC (fun _ => ENNReal.toReal_nonneg)
    hG8 hR128 hR0 (3683/2500) (3/10^46) g4 g8 (by norm_num) (by norm_num)
    (by dsimp only [g4]; positivity) (by dsimp only [g8]; positivity) hRcap hG4cap hG8cap hrare.2.2 hrestore
  have heX : eLpNorm X 2 μ=eLpNorm (parentBoundaryBandMaxTraceHistory M n height P t) 2 μ :=
    parent_history_toReal_norm μ _ (ae_of_all _ (fun ω => (parent_history_sample_finite M P n height t ω).1.ne)) 2
  have heC : eLpNorm C 20 μ=eLpNorm (parentBoundaryCommonCenteredMaxHistory M P n height t) 20 μ :=
    parent_history_toReal_norm μ _ (ae_of_all _ (fun ω => (parent_history_sample_finite M P n height t ω).2.ne)) 20
  rw [←heX]
  apply hpay.trans_eq
  rw [heC]
  congr 1
  congr 1
  dsimp only [g4,g8,V,μ]
  rw [show 2*t*parentBoundaryCommonBandVariance M h n height=
    2*(t*parentBoundaryCommonBandVariance M h n height) by ring,
    Real.sqrt_mul (by norm_num : (0:ℝ)≤2) (3683/2500),
    Real.sqrt_mul (by norm_num : (0:ℝ)≤2) (t*parentBoundaryCommonBandVariance M h n height)]
  ring

end
end ASDExplicitGamma.Native
