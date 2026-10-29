module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalBandVariance
public import ASDExplicitGamma.Inverse.LaterBandDerivative

/-! Identification of the actual compact band tensor with its Sobolev witness. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization Gaussian Model Inverse Triadic MeasureTheory
open Algsuperdiff.Section3
open scoped BigOperators
noncomputable section

/-- Exact reindexing of the physical finite band, including arbitrary negative
left labels and the empty band. -/
theorem upper_cell_physical_band_sum' {E : Type*} [AddCommMonoid E]
    (n : ℤ) (height : ℕ) (f : ℤ → E) :
    (∑ i : Fin height, f (upperCellPhysicalBandLabel n height i)) =
      ∑ k ∈ Finset.Ioc n (n+(height:ℤ)), f k := by
  apply Finset.sum_bij (fun i _ => upperCellPhysicalBandLabel n height i)
  · intro i _
    simp only [Finset.mem_Ioc, upperCellPhysicalBandLabel]
    have hi := i.isLt
    omega
  · intro i _ j _ hij
    exact upper_cell_physical_band_label_injective n height hij
  · intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    let i : Fin height := ⟨(k-n-1).toNat, by omega⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    dsimp only [upperCellPhysicalBandLabel,i]
    omega
  · intro i _
    rfl

/-- The Gaussian full-band tensor is exactly the tensor of the genuine smooth
Sobolev band; no triangle over shell suprema is used. -/
theorem upper_cell_band_sobolev_tensor_eq {ι : Type} [Fintype ι]
    (o : ι → Q3SpatialJet) (n : ℤ) (height : ℕ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    upperCellBandTensor (upperCellPhysicalBandLabel n height)
      (fun i => weights (upperCellPhysicalBandLabel n height i)) o x ω =
      laterBandTensor o n (n+(height:ℤ)) weights ω x := by
  have he : upperCellBandTensor (upperCellPhysicalBandLabel n height)
      (fun i => weights (upperCellPhysicalBandLabel n height i)) o x ω =
      ∑ i : Fin height, weights (upperCellPhysicalBandLabel n height i) •
        supMeanShellTensor o x (ω.val (upperCellPhysicalBandLabel n height i)) := by
    ext a
    simp only [upperCellBandTensor, upperCellBandJet, WithLp.ofLp_sum,
      Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, supMeanShellTensor,
      supMeanShellJetScalar, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  exact upper_cell_physical_band_sum' n height
    (fun k => weights k • supMeanShellTensor o x (ω.val k))

/-- Pointwise actual Sobolev tensor norms are bounded by the full compact band
norm on the exact physical observation square. -/
theorem upper_cell_band_sobolev_tensor_norm_le {ι : Type} [Fintype ι]
    (Q : TriadicCube 2) (o : ι → Q3SpatialJet) (n : ℤ) (height : ℕ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    {x : Vec 2} (hx : x ∈ cubeSet Q) :
    ‖laterBandTensor o n (n+(height:ℤ)) weights ω x‖ ≤
      ‖upperCellBandSquareTensor (upperCellPhysicalBandLabel n height)
        (fun i => weights (upperCellPhysicalBandLabel n height i)) o
        (cubeCenter Q) (cubeScaleFactor Q) ω‖ := by
  rw [← upper_cell_band_sobolev_tensor_eq]
  exact (upperCellBandSquareTensor (upperCellPhysicalBandLabel n height)
    (fun i => weights (upperCellPhysicalBandLabel n height i)) o
      (cubeCenter Q) (cubeScaleFactor Q) ω).norm_coe_le_norm
        ⟨x,cube_subset_closed_observation Q hx⟩

end
end ASDExplicitGamma.Scalar
