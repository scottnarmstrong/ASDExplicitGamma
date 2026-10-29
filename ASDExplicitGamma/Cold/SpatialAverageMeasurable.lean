module

public import ASDExplicitGamma.Cold.CanonicalAverageMeasurable
public import ASDExplicitGamma.Cold.SquareCellMean
public import Homogenization.Multiscale.ProjectionConvergence
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Joint representatives from measurable cell averages, with no measurable-solution premise -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- Measurable averages on the countable triadic partitions produce a jointly measurable
representative of every spatially integrable sample. Equality is spatial a.e. at almost every sample. -/
theorem cold_joint_representative_of_cell_averages {Ω : Type*} [MeasurableSpace Ω]
    (μprob : Measure Ω) (Q : TriadicCube 2) (f : Ω → Vec 2 → ℝ)
    (hf : ∀ ω, IntegrableOn (f ω) (cubeSet Q))
    (havg : ∀ r, ∀ C : SquareCells Q r, AEMeasurable (fun ω => cubeAverage C.val (f ω)) μprob) :
    ∃ g : Ω × Vec 2 → ℝ, StronglyMeasurable g ∧
      ∀ᵐ ω ∂μprob, (fun x => g (ω,x)) =ᵐ[volume.restrict (cubeSet Q)] f ω := by
  classical
  let b := fun r (C : SquareCells Q r) => (havg r C).mk (fun ω => cubeAverage C.val (f ω))
  have hb (r : ℕ) (C : SquareCells Q r) : Measurable (b r C) := (havg r C).measurable_mk
  have he : ∀ᵐ ω ∂μprob, ∀ r, ∀ C : SquareCells Q r, b r C ω = cubeAverage C.val (f ω) := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro C
    exact (havg r C).ae_eq_mk.symm
  let P := fun (r : ℕ) (z : Ω × Vec 2) => ∑ C : SquareCells Q r, if z.2 ∈ cubeSet C.val then b r C z.1 else 0
  have hP (r : ℕ) : StronglyMeasurable (P r) := by
    apply Measurable.stronglyMeasurable
    apply Finset.measurable_sum
    intro C _
    exact Measurable.ite ((measurableSet_cubeSet C.val).preimage measurable_snd)
      ((hb r C).comp measurable_fst) measurable_const
  let g := fun z : Ω × Vec 2 => limUnder atTop (fun r => P r z)
  refine ⟨g,StronglyMeasurable.limUnder hP,?_⟩
  filter_upwards [he] with ω hω
  have hPe (r : ℕ) (x : Vec 2) : P r (ω,x) = cubeProjection Q r (f ω) x := by
    dsimp only [P,cubeProjection]
    simp_rw [hω]
    exact Finset.sum_attach (descendantsAtDepth Q r) (fun C => if x ∈ cubeSet C then cubeAverage C (f ω) else 0)
  filter_upwards [ae_tendsto_cubeProjection_of_integrableOn Q (f ω) (hf ω)] with x hx
  change limUnder atTop (fun r => P r (ω,x)) = f ω x
  simp_rw [hPe]
  exact hx.limUnder_eq

/-- Ordinary weighted squared spatial energies are a.e. measurable from the actual cell averages.
No joint measurability of the initially chosen spatial representative is required. -/
theorem cold_weighted_square_average_measurable {Ω : Type*} [MeasurableSpace Ω]
    (μprob : Measure Ω) (Q : TriadicCube 2) (f : Ω → Vec 2 → ℝ)
    (hf : ∀ ω, IntegrableOn (f ω) (cubeSet Q))
    (havg : ∀ r, ∀ C : SquareCells Q r, AEMeasurable (fun ω => cubeAverage C.val (f ω)) μprob)
    (φ : Vec 2 → ℝ) (hφ : Measurable φ) :
    AEStronglyMeasurable (fun ω => cubeAverage Q (fun x => φ x*(f ω x)^2)) μprob := by
  obtain ⟨g,hg,he⟩ := cold_joint_representative_of_cell_averages μprob Q f hf havg
  have hprod : StronglyMeasurable (fun z : Ω × Vec 2 => φ z.2*(g z)^2) :=
    ((hφ.comp measurable_snd).stronglyMeasurable).mul (hg.pow 2)
  have hm := hprod.integral_prod_right' (ν := volume.restrict (cubeSet Q))
  have hmeas := hm.const_mul (cubeVolume Q)⁻¹
  apply hmeas.aestronglyMeasurable.congr
  filter_upwards [he] with ω hω
  unfold cubeAverage
  congr 1
  apply integral_congr_ae
  filter_upwards [hω] with x hx
  rw [hx]

end ASDExplicitGamma.Cold
