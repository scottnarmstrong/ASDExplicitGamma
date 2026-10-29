module

public import ASDExplicitGamma.Cold.CanonicalEnergyMeasurable
public import ASDExplicitGamma.Cold.MatchedCutoffBound
public import ASDExplicitGamma.Cold.NativeSubadditivity

/-! # Ordinary integrability of the actual native cutoff energies -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Homogenization.Book Algsuperdiff.Section3
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- The actual native four-load energy weighted by any parent cutoff. -/
def coldNativeMatchedCutoff (M : ABKModel 2) (m : ℤ) (Q R : TriadicCube 2) (ω : Cutoff.CutoffSample 2) : ℝ :=
  volumeAverage (openCubeSet R) (fun x => plateauOnSquare Q x*squareMatchedDensity R (coldNativeMatchedOptimizers M m R ω) x)

/-- Both native coefficient choices have the exact canonical weighted-energy measurability. -/
theorem coldNativeMatchedCutoff_aestronglyMeasurable (M : ABKModel 2) (m : ℤ) (Q R : TriadicCube 2) :
    AEStronglyMeasurable (coldNativeMatchedCutoff M m Q R) (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μprob := (Cutoff.cutoffSampleLaw M).toMeasure
  have hp (i : Fin 2) := cold_canonical_weighted_energy_measurable μprob (coldNativeCoefficient M m)
    (coldNativeCoefficient_measurable M m) (coldNativeCoefficient_locallyElliptic M m)
    (coldNativeCoefficient_symmPart M m) R (Pi.single i 1) (Pi.single i 1) (plateauOnSquare Q)
    (lipschitzWith_plateauOnSquare Q).continuous.measurable (norm_plateauOnSquare_le Q)
  have ha (i : Fin 2) := cold_canonical_weighted_energy_measurable μprob (fun ω => adjointReg (coldNativeCoefficient M m ω))
    (measurable_adjointReg.comp (coldNativeCoefficient_measurable M m)) (coldNativeAdjoint_locallyElliptic M m)
    (coldNativeAdjoint_symmPart M m) R (Pi.single i 1) (Pi.single i 1) (plateauOnSquare Q)
    (lipschitzWith_plateauOnSquare Q).continuous.measurable (norm_plateauOnSquare_le Q)
  have hh := Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (hp i).add (ha i))
  have he (ω : Cutoff.CutoffSample 2) : coldNativeMatchedCutoff M m Q R ω =
      ∑ i : Fin 2, (cubeAverage R (fun x => plateauOnSquare Q x*scalarVariationEnergyIntegrand
        (coldNativeCoefficient M m ω).toFun (coldNativeOptimizer M m R (Pi.single i 1) (Pi.single i 1) ω) x) +
        cubeAverage R (fun x => plateauOnSquare Q x*scalarVariationEnergyIntegrand
          (adjointReg (coldNativeCoefficient M m ω)).toFun
          (coldCanonicalOptimizer (adjointReg (coldNativeCoefficient M m ω)) (coldNativeAdjoint_locallyElliptic M m ω)
            R (Pi.single i 1) (Pi.single i 1)) x)) := by
    obtain ⟨Λ,hE⟩ := coldNativeCoefficient_elliptic M m R ω
    have hO := hE.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
    unfold coldNativeMatchedCutoff squareMatchedDensity
    rw [square_four_weighted_average Q R _ _
      (fun i => integrable_plateau_local_energy Q R hO ((coldNativeMatchedOptimizers M m R ω).primal i))
      (fun i => integrable_plateau_local_energy Q R (isEllipticFieldOn_adjointCoeffField hO)
        ((coldNativeMatchedOptimizers M m R ω).adjoint i))]
    simp only [square_volumeAverage_eq_cubeAverage]
    rfl
  apply hh.congr
  exact Filter.Eventually.of_forall (fun ω => (he ω).symm)

/-- These ordinary cutoff energies are integrable, with domination by the genuine integrable trace. -/
theorem coldNativeMatchedCutoff_integrable (M : ABKModel 2) (m : ℤ) (Q R : TriadicCube 2) :
    Integrable (coldNativeMatchedCutoff M m Q R) (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply ((coldNativeCellTrace_integrable M m R).const_mul (24/7:ℝ)).mono'
    (coldNativeMatchedCutoff_aestronglyMeasurable M m Q R)
  apply Filter.Eventually.of_forall
  intro ω
  obtain ⟨Λ,hE⟩ := coldNativeCoefficient_elliptic M m R ω
  have hO := hE.mono (measurableSet_openCubeSet R) (openCubeSet_subset_cubeSet R)
  have hb := square_matched_cutoff_bounds Q R hO (coldNativeMatchedOptimizers M m R ω)
  change ‖coldNativeMatchedCutoff M m Q R ω‖ ≤ (24/7:ℝ)*coldNativeCellTrace M m R ω
  unfold coldNativeMatchedCutoff
  rw [Real.norm_eq_abs,abs_of_nonneg hb.1,coldNativeCellTrace_eq_normalized]
  exact hb.2

/-- The actual P4 family has every required ordinary expectation, at arbitrary depth. -/
theorem coldNativePlateauFamily_recoveryIntegrable (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (r : ℕ) :
    ColdRecoveryIntegrable ((coldNativePlateauFamily M m Q).atDepth r) (Cutoff.cutoffSampleLaw M).toMeasure where
  parentTrace := (coldNativeCellTrace_integrable M m Q).congr
    (Filter.Eventually.of_forall (fun ω => (coldNativePlateauFamily_parentTrace M m Q r ω).symm))
  cellTrace := fun C => (coldNativeCellTrace_integrable M m C.val).congr
    (Filter.Eventually.of_forall (fun ω => (coldNativePlateauFamily_cellTrace M m Q r C ω).symm))
  parentCutoffEnergy := coldNativeMatchedCutoff_integrable M m Q Q
  cellCutoffEnergy := fun C => coldNativeMatchedCutoff_integrable M m Q C.val

end ASDExplicitGamma.Cold
