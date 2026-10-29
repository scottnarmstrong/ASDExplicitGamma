module

public import ASDExplicitGamma.Cold.SpatialAverageMeasurable
public import ASDExplicitGamma.Cold.NativeScalarEnergy

/-! # Ordinary weighted energies of actual canonical optimizers are measurable -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Homogenization.Book
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- The weighted canonical energy for a genuine scalar-symmetric family is a.e. measurable.
The proof constructs joint spatial gradient representatives from actual measurable cell averages. -/
theorem cold_canonical_weighted_energy_measurable {Ω : Type*} [MeasurableSpace Ω]
    (μprob : Measure Ω) [IsProbabilityMeasure μprob] (a : Ω → RegCoeffField 2)
    (hm : Measurable a) (ha : ∀ ω, Ch04.AELocallyUniformlyEllipticField (a ω))
    {ν : ℝ} (hsym : ∀ ω x, symmPart ((a ω).toFun x) = ν • (1:Mat 2))
    (Q : TriadicCube 2) (p q : Vec 2) (φ : Vec 2 → ℝ) (hφ : Measurable φ)
    {B : ℝ} (hB : ∀ x, ‖φ x‖ ≤ B) :
    AEStronglyMeasurable (fun ω => cubeAverage Q (fun x => φ x*
      scalarVariationEnergyIntegrand (a ω).toFun (coldCanonicalOptimizer (a ω) (ha ω) Q p q) x)) μprob := by
  let v := fun ω => coldCanonicalOptimizer (a ω) (ha ω) Q p q
  have hgrad (ω : Ω) (i : Fin 2) : IntegrableOn (fun x => v ω |>.toH1.grad x i) (cubeSet Q) := by
    apply integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr
    exact ((v ω).toH1.gradMemL2 i).integrable (by norm_num)
  have havg (i : Fin 2) (r : ℕ) (C : SquareCells Q r) :
      AEMeasurable (fun ω => cubeAverage C.val (fun x => (v ω).toH1.grad x i)) μprob :=
    (aemeasurable_pi_iff.mp (cold_canonical_gradient_average_measurable μprob a hm ha Q C.val C.property p q)) i
  have hmeas (i : Fin 2) := cold_weighted_square_average_measurable μprob Q
    (fun ω x => (v ω).toH1.grad x i) (fun ω => hgrad ω i) (havg i) φ hφ
  have hsq (ω : Ω) (i : Fin 2) : IntegrableOn (fun x => φ x*((v ω).toH1.grad x i)^2) (cubeSet Q) := by
    have hi : IntegrableOn (fun x => ((v ω).toH1.grad x i)^2) (cubeSet Q) :=
      integrableOn_cubeSet_iff_integrableOn_openCubeSet.mpr ((v ω).toH1.gradMemL2 i).integrable_sq
    exact hi.bdd_mul hφ.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have he (ω : Ω) : cubeAverage Q (fun x => φ x*scalarVariationEnergyIntegrand (a ω).toFun (v ω) x) =
      ν*∑ i : Fin 2, cubeAverage Q (fun x => φ x*((v ω).toH1.grad x i)^2) := by
    have hp : (fun x => φ x*scalarVariationEnergyIntegrand (a ω).toFun (v ω) x) =
        (fun x => ν*∑ i : Fin 2, φ x*((v ω).toH1.grad x i)^2) := by
      funext x
      rw [cold_scalar_energy_integrand (hsym ω)]
      rw [← Finset.mul_sum]
      ring
    rw [hp]
    unfold cubeAverage
    rw [integral_const_mul,integral_finsetSum Finset.univ (fun i _ => hsq ω i)]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hh : AEStronglyMeasurable (fun ω => ν*∑ i : Fin 2, cubeAverage Q (fun x => φ x*((v ω).toH1.grad x i)^2)) μprob :=
    (Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hmeas i)).const_mul ν
  change AEStronglyMeasurable (fun ω => cubeAverage Q (fun x => φ x*scalarVariationEnergyIntegrand (a ω).toFun (v ω) x)) μprob
  simp_rw [he]
  exact hh

end ASDExplicitGamma.Cold
