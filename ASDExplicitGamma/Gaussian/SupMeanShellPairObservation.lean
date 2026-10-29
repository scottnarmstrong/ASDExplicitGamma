module

public import ASDExplicitGamma.Gaussian.SupMeanShellSupremum
public import ASDExplicitGamma.Gaussian.SupMeanCompactPairConcentration

/-! Fixed finite-jet observations of the actual combined shell tensor supremum. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open TopologicalSpace Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section
section
variable (c : Vec 2) (s : ℝ) [Nonempty (supMeanClosedSquare c s)]

/-- The two tensor orders use separate fixed locations and unit-ball directions. -/
def supMeanShellPairPoint (n : ℕ) (i : Fin 2 ⊕ (Fin 2 × Fin 2)) : Q3SpatialJet × Vec 2 :=
  match i with
  | .inl d => (.first d, (denseSeq (supMeanClosedSquare c s) n.unpair.1.unpair.1).val)
  | .inr d => (.second d.1 d.2, (denseSeq (supMeanClosedSquare c s) n.unpair.2.unpair.1).val)

/-- These coefficients are fixed independently of the Gaussian sample. -/
def supMeanShellPairCoefficient (a b : ℝ) (n : ℕ) (i : Fin 2 ⊕ (Fin 2 × Fin 2)) : ℝ :=
  match i with
  | .inl d => a*(supMeanNormingVector (EuclideanSpace ℝ (Fin 2)) n.unpair.1.unpair.2) d
  | .inr d => b*(supMeanNormingVector (EuclideanSpace ℝ (Fin 2 × Fin 2)) n.unpair.2.unpair.2) d

/-- The compact pair projection is literally a finite linear combination of
stored shell jets; its locations are not selected from the sample. -/
theorem supMean_shell_pair_observation_eq (a b : ℝ) (n : ℕ) (j : ShellField 2) :
    supMeanCompactPairProjection (supMeanShellSquareTensor Q3SpatialJet.first c s j)
      (supMeanShellSquareTensor (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j) a b n =
    ∑ i, supMeanShellPairCoefficient a b n i *
      supMeanShellJetScalar (supMeanShellPairPoint c s n i).1 (supMeanShellPairPoint c s n i).2 j := by
  simp only [supMeanCompactPairProjection, supMeanCompactProjection,
    supMeanShellSquareTensor, ContinuousMap.coe_mk, supMeanShellTensor,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial,
    Fintype.sum_sum_type, supMeanShellPairPoint, supMeanShellPairCoefficient,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- The actual combined countable observations are jointly centered Gaussian. -/
theorem supMean_shell_pair_gaussian (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (a b : ℝ) :
    IsCenteredGaussianFamily (ShellField.shellMarginalLaw M.P k).toMeasure
      (fun n j => supMeanCompactPairProjection (supMeanShellSquareTensor Q3SpatialJet.first c s j)
        (supMeanShellSquareTensor (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j) a b n) := by
  have hg := (supMean_shell_jets_gaussian M h hM k).finite_linear_image
    (supMeanShellPairPoint c s) (supMeanShellPairCoefficient a b)
  simpa only [supMean_shell_pair_observation_eq] using! hg

end
end
end ASDExplicitGamma.Gaussian
