module

public import ASDExplicitGamma.Scalar.OldHessianTrialCoarsePotential
public import ASDExplicitGamma.Scalar.OldHessianTrialColumnSource
public import ASDExplicitGamma.Native.OldSignedHaarCongr

/-! Literal coarse-cell aggregation of the retained source product. The
coarse potential is restricted to fine children; it is never re-solved there. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Main Triadic Gaussian Response Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The genuine coarse cell-zero bottom first potential on a named member
of the actual parent partition. -/
def oldHessianCoarseCellPotential (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2)
    (D : OldSignedCellIndex Q coarse) : H10Function (openCubeSet D.val) :=
  oldSignedCellFirstCorrector Q D.val (openCubeSet_subset_of_mem_descendantsAtDepth D.property)
    nu sigma hnu hsigma k (fun _ => (0,e)) (memLp_const (0,e))

/-- On every actual fine child, the retained globally glued product is the
literal coarse-cell product a.e., with the identical physical direction. -/
theorem old_hessian_patched_product_restrict (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (j : whiteBasisIndex)
    (D : OldSignedCellIndex Q coarse) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth D.val 1) :
    oldHessianCoarseProduct Q b L
      (oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k e) (whiteBasis j) =ᵐ[
        volumeMeasureOn (openCubeSet U)]
      oldHessianCoarseProduct D.val b L
        (oldHessianCoarseCellPotential Q coarse nu sigma hnu hsigma k e D) (whiteBasis j) := by
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet U)] with x hx
  have hxD := openCubeSet_subset_of_mem_descendantsAtDepth hU hx
  change (oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k e).toH1Function x • _ = _
  rw [old_hessian_coarse_potential_cell Q coarse nu sigma hnu hsigma k e D.val D.property x hxD]
  rfl

/-- One actual full-mode product energy splits exactly into the coarse
partition and its nine-child fine positive norms. -/
theorem old_hessian_patched_product_partition (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (j : whiteBasisIndex) :
    descendantsAverage Q (coarse+1) (fun U => vectorPositiveHaarEnergy U
      (oldHessianCoarseProduct Q b L
        (oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k e) (whiteBasis j))) =
      oldSignedCellAverage Q coarse (fun D => descendantsAverage D.val 1 (fun U =>
        vectorPositiveHaarEnergy U (oldHessianCoarseProduct D.val b L
          (oldHessianCoarseCellPotential Q coarse nu sigma hnu hsigma k e D) (whiteBasis j)))) := by
  let F := oldHessianCoarseProduct Q b L
    (oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k e) (whiteBasis j)
  have he : oldSignedCellAverage Q coarse (fun D => descendantsAverage D.val 1 (fun U =>
      vectorPositiveHaarEnergy U (oldHessianCoarseProduct D.val b L
        (oldHessianCoarseCellPotential Q coarse nu sigma hnu hsigma k e D) (whiteBasis j)))) =
      oldSignedCellAverage Q coarse (fun D => descendantsAverage D.val 1 (fun U => vectorPositiveHaarEnergy U F)) := by
    unfold oldSignedCellAverage
    congr 1
    apply Finset.sum_congr rfl
    intro D _
    unfold descendantsAverage
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    exact (old_signed_coordinate_primal_sum_congr U (Real.sqrt 3)
      (old_hessian_patched_product_restrict Q coarse nu sigma hnu hsigma k e b L j D U hU)).symm
  rw [he,old_signed_cell_average_eq_descendantsAverage Q coarse
    (fun D => descendantsAverage D 1 (fun U => vectorPositiveHaarEnergy U F))]
  exact descendantsAverage_succ_eq_descendantsAverage_descendantsAverage Q coarse _

/-- Summation over the entire white family and actual coarse partition,
with the sharp coarse product payments still attached to each cell. -/
theorem old_hessian_patched_product_energy (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let E := fun j : whiteBasisIndex => descendantsAverage Q (coarse+1) (fun U =>
      vectorPositiveHaarEnergy U (oldHessianCoarseProduct Q b L
        (oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k e) (whiteBasis j)))
    Summable E ∧ (∑' j,E j) ≤ oldSignedCellAverage Q coarse (fun D =>
      (Real.sqrt 2*((503/200:ℝ)*(cubeScaleFactor D.val/L.1)+
        (2031/500:ℝ)*(cubeScaleFactor D.val/L.1)^2)*|b|)^2*
      vectorWeakHaarEnergy D.val
        (oldHessianCoarseCellPotential Q coarse nu sigma hnu hsigma k e D).toH1Function.grad) := by
  intro E
  let Y := fun (j : whiteBasisIndex) (D : OldSignedCellIndex Q coarse) =>
    descendantsAverage D.val 1 (fun U => vectorPositiveHaarEnergy U
      (oldHessianCoarseProduct D.val b L
        (oldHessianCoarseCellPotential Q coarse nu sigma hnu hsigma k e D) (whiteBasis j)))
  have hlocal (D : OldSignedCellIndex Q coarse) := old_hessian_coarse_product_broken D.val b L
    (oldHessianCoarseCellPotential Q coarse nu sigma hnu hsigma k e D)
  have he (j : whiteBasisIndex) : E j=oldSignedCellAverage Q coarse (Y j) :=
    old_hessian_patched_product_partition Q coarse nu sigma hnu hsigma k e b L j
  have hs : Summable (fun j => oldSignedCellAverage Q coarse (Y j)) :=
    (summable_sum (fun D _ => (hlocal D).1)).mul_left (((descendantsAtDepth Q coarse).card:ℝ)⁻¹)
  have hsum : (∑' j,oldSignedCellAverage Q coarse (Y j))=
      oldSignedCellAverage Q coarse (fun D => ∑' j,Y j D) := by
    unfold oldSignedCellAverage
    rw [tsum_mul_left,Summable.tsum_finsetSum (fun D _ => (hlocal D).1)]
  refine ⟨hs.congr (fun j => (he j).symm),?_⟩
  simp_rw [he]
  rw [hsum]
  exact old_signed_cell_average_mono Q coarse (fun D => (hlocal D).2)

end
end ASDExplicitGamma.Scalar
