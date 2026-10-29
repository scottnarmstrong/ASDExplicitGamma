module

public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocks
public import ASDExplicitGamma.Native.HeatRefinedObserverHistory
public import ASDExplicitGamma.Native.HeatRefinedTranslatedLaw

/-! The ORIGINAL rare bank controls all refined source drift shells and
all auxiliary shears, before any child or probability average. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic Algsuperdiff.Section3
noncomputable section

/-- The literal bank maximum in a refined source row, keeping the parent
true frame and the source's shell-dependent observation mesh. -/
def heatVHEATDriftBank (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (g : ℝ) (d : Fin 9) : ℝ :=
  let Q := originCube 2 (n-1)
  let j := pureFluxBankSourceDepth (d.val+2)
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
    (pureFluxOpenResponseRestriction (n-1) (heatRefinedObserverShear (n-1) n height t ω g))
  max (lemmaVTileHistory Q j a) (pureFluxSourceTileHistory Q j a)

/-- The actual source bank is nonnegative at every sample and shear. -/
theorem heatVHEATDrift_bank_nonneg (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (g : ℝ) (d : Fin 9) :
    0 ≤ heatVHEATDriftBank M n height t ω g d :=
  (lemmaVTileHistory_nonneg _ _ _).trans (le_max_left _ _)

/-- One genuine physical bank event controls every refined mesh and every
auxiliary gauge. The remainder and its original reserve are unchanged. -/
theorem heatVHEATDrift_bank_ae_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hpast : ∀ l<n,nativeInductionState M h l) (t : ℝ) (ht : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,∀ g : ℝ,∀ d : Fin 9,
      heatVHEATDriftBank M n height t ω g d ≤
        (3683/2500:ℝ)+nativeSourceBandRemainder M n height t ω := by
  have hb := native_source_band_history_rare_split M h hM hg n height hpast t ht
  have hq : originCube 2 (n-1)∈descendantsAtDepth (originCube 2 n) 1 := by
    simpa only [Nat.cast_one] using originCube_mem_descendantsAtDepth' 2 n 1
  filter_upwards [hb.1,hb.2.2.2.2] with ω hfinite hrare
  intro g d
  let Q := originCube 2 (n-1)
  let j := pureFluxBankSourceDepth (d.val+2)
  let k := pureFluxOpenResponseRestriction (n-1) (heatRefinedObserverShear (n-1) n height t ω g)
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n) k
  have hj : 1+j ≤ 5 := by dsimp only [j,pureFluxBankSourceDepth]; omega
  have hsource := pureFlux_source_tile_history_le Q j a
    ((3683/2500:ℝ)+nativeSourceBandRemainder M n height t ω) (by
      intro U hU
      change lemmaVInverseHistory U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
          (pureFluxOpenResponseRestriction (n-1)
            (parentBoundaryObserverBandScalar (n-1) n height t ω+ContinuousMap.const _ g)))
        ((3:ℝ)^(1/4:ℝ)) ≤ _
      rw [parent_boundary_inverse_history_gauge (n-1) M.nu (Annealed.sigmaBar M n)
        M.nu_pos (Annealed.sigmaBar_characterization M n).1 _ g U j hU,
        heat_refined_observer_history_eq_parent M (n-1) n 1 hq height t ω U j hU]
      exact (native_source_band_mesh_history_le M n height t ω (1+j) hj hfinite.ne
        (mem_descendantsAtDepth_add hq hU)).trans hrare)
  exact max_le ((tile_history_le_source_history Q j M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 k).trans hsource) hsource

/-- Each translated child keeps its OWN original remainder on the common
physical/auxiliary law. Neither child independence nor a maximum is taken. -/
theorem heatVHEATDrift_bank_family_ae_le {I : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hpast : ∀ l<n,nativeInductionState M h l) (t : ℝ) (ht : t ≤ 1)
    (s : Finset I) (shift : I → Vec 2) (g : I → (ℕ → ℝ) → ℝ) :
    ∀ᵐ z ∂nativeHeatRemainderJointLaw M,∀ i∈s,∀ d : Fin 9,
      heatVHEATDriftBank M n height t (Cutoff.translateCutoffSample (shift i) z.1) (g i z.2) d ≤
        (3683/2500:ℝ)+heatRefinedTranslatedRare M n height t (shift i) z := by
  have hrow := heatVHEATDrift_bank_ae_le M h hM hg n height hpast t ht
  have hjoint : ∀ᵐ z ∂nativeHeatRemainderJointLaw M,∀ a : ℝ,∀ d : Fin 9,
      heatVHEATDriftBank M n height t z.1 a d ≤
        (3683/2500:ℝ)+nativeSourceBandRemainder M n height t z.1 :=
    (measurePreserving_fst (μ := (Cutoff.cutoffSampleLaw M).toMeasure)
      (ν := standardGaussianInfinitePi)).quasiMeasurePreserving.ae hrow
  apply (Finset.eventually_all s).2
  intro i _
  have hs := (heat_refined_joint_shift_preserving M (shift i)).quasiMeasurePreserving.ae hjoint
  filter_upwards [hs] with z hz
  intro d
  exact hz (g i z.2) d

end
end ASDExplicitGamma.Native
