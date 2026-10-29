module

public import ASDExplicitGamma.Native.ParentBoundarySourceProjection
public import ASDExplicitGamma.Native.OldSignedSeriesLinearBudget
public import ASDExplicitGamma.Native.OldSignedQ3SourceEnergy

/-! Complete cellwise four-load weighted projection budgets for the
actual parent source. Histories remain in their original common medium. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- Actual complete four-load source size on a comparison cell. -/
def parentBoundaryCellSourceSize (Q U : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  Real.sqrt (∑' n : whiteBasisIndex,∑ c : BlockCoord 2,vectorPositiveHaarNorm U
    (fun x => (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (blockBasis c) x).2)^2)

/-- Complete mode convergence holds individually on every actual fine
cell, with its positive averaging weight retained. -/
theorem parent_boundary_cell_source_series (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    Summable (fun n : whiteBasisIndex => ∑ c : BlockCoord 2,vectorPositiveHaarNorm U
      (fun x => (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (blockBasis c) x).2)^2) := by
  apply summable_sum
  intro c _
  exact old_signed_summable_of_descendant_average Q depth _
    (fun _ _ _ => sq_nonneg _)
    (parent_boundary_actual_source_trace Q depth nu sigma hnu hsigma k (blockBasis c) b L).1 U hU

/-- Both complete four-load source projection budgets use the actual
inverse history; direction-dependent lift potentials are retained. -/
theorem parent_boundary_cell_source_budget (Q U : TriadicCube 2) (depth : ℕ)
    (hU : U ∈ descendantsAtDepth Q depth)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let R := fun n c => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k
      (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (blockBasis c))
      (parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n (blockBasis c))
    let v := fun n c => parentBoundaryCellSourcePotential Q U hsub nu sigma hnu hsigma k b L n (blockBasis c)
    let E := fun n => ∑ c : BlockCoord 2,oldSignedEnergyPairing U nu sigma kU (R n c) (R n c)
    let K := fun n => ∑ c : BlockCoord 2,vectorWeakHaarNorm U (v n c).toH1Function.grad^2
    Summable E ∧ (∑' n,E n)≤oldSignedInverseHistory U a*parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L^2 ∧
    Summable K ∧ Real.sqrt (∑' n,K n)≤(1+inverseHistoryDiscount)*oldSignedInverseHistory U a*
      parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L := by
  intro hsub a kU R v E K
  let p := fun n c => vectorPositiveHaarNorm U
    (fun x => (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (blockBasis c) x).2)
  let g := fun n c => vectorWeakHaarNorm U (v n c).toH1Function.grad
  have hps := parent_boundary_cell_source_series Q U depth hU nu sigma hnu hsigma k b L
  have hB : 0≤oldSignedInverseHistory U a :=
    lemmaVInverseHistory_nonneg U a (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hE (n : whiteBasisIndex) : 0≤E n := by
    apply Finset.sum_nonneg
    intro c _
    have hR : MemBlockL2 (openCubeSet U) (R n c) := Lp.memLp (R n c)
    rw [←old_signed_energy_inner_fields U nu sigma hnu hsigma kU hR hR]
    exact real_inner_self_nonneg
  have hpoint (n : whiteBasisIndex) : E n≤oldSignedInverseHistory U a*(∑ c : BlockCoord 2,p n c^2) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
      (parent_boundary_actual_source_sharp Q U depth hU nu sigma hnu hsigma k (blockBasis c) b L n).1)
    simpa only [←Finset.mul_sum] using hh
  have hEs := (hps.mul_left (oldSignedInverseHistory U a)).of_nonneg_of_le hE hpoint
  have hEt := hEs.tsum_le_tsum hpoint (hps.mul_left (oldSignedInverseHistory U a))
  rw [tsum_mul_left] at hEt
  have hd0 : 0≤∑' n : whiteBasisIndex,∑ c : BlockCoord 2,p n c^2 :=
    tsum_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hdeq : parentBoundaryCellSourceSize Q U nu sigma hnu hsigma k b L^2=
      ∑' n : whiteBasisIndex,∑ c : BlockCoord 2,p n c^2 := Real.sq_sqrt hd0
  have hD : 0≤1+inverseHistoryDiscount := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have hfirst := old_signed_load_series_linear_budget p p g
    ((1+inverseHistoryDiscount)*oldSignedInverseHistory U a) 0
    (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _) (fun _ _ => Real.sqrt_nonneg _)
    (mul_nonneg hD hB) le_rfl hps hps (fun n c => by
      simpa only [zero_mul,add_zero] using
        (parent_boundary_actual_source_sharp Q U depth hU nu sigma hnu hsigma k (blockBasis c) b L n).2)
  refine ⟨hEs,?_,hfirst.1,?_⟩
  · rw [hdeq]
    exact hEt
  · simpa only [zero_mul,add_zero,K,g,parentBoundaryCellSourceSize,p] using hfirst.2

end
end ASDExplicitGamma.Native
