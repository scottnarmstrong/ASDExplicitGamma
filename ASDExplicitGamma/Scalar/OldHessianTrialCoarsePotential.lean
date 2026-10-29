module

public import ASDExplicitGamma.Native.OldSignedCellPotentials
public import Homogenization.Sobolev.W1p.ZeroExtensionGraph

/-! Genuine coarse cell-zero potentials glued on the parent. These are built
from the same physical weighted residuals used by the source partition. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response
noncomputable section

/-- Finite H10 sums retain their literal functions and gradients. We construct
the sum without imposing algebraic identities on approximation sequences. -/
theorem old_hessian_h10_sum_exists {ι : Type*} {U : Set (Vec 2)}
    (s : Finset ι) (f : ι → H10Function U) :
    ∃ u : H10Function U,
      u.toH1Function.toFun = (fun x => ∑ i ∈ s, (f i).toH1Function x) ∧
      u.toH1Function.grad = (fun x => ∑ i ∈ s, (f i).toH1Function.grad x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨0,?_,?_⟩
    · funext x
      change (0:ℝ) = _
      simp
    · funext x
      change (0:Vec 2) = _
      simp
  | @insert i s hi hs =>
    obtain ⟨u,hu,hg⟩ := hs
    refine ⟨f i+u,?_,?_⟩
    · change (f i).toH1Function.toFun+u.toH1Function.toFun = _
      rw [hu]
      funext x
      simp only [Pi.add_apply,Finset.sum_insert hi]
    · change (f i).toH1Function.grad+u.toH1Function.grad = _
      rw [hg]
      funext x
      simp only [Pi.add_apply,Finset.sum_insert hi]

/-- Select the finite genuine H10 sum from its proved function/gradient data. -/
def oldHessianH10Sum {ι : Type*} {U : Set (Vec 2)}
    (s : Finset ι) (f : ι → H10Function U) : H10Function U :=
  (old_hessian_h10_sum_exists s f).choose

theorem old_hessian_h10_sum_fun {ι : Type*} {U : Set (Vec 2)}
    (s : Finset ι) (f : ι → H10Function U) :
    (oldHessianH10Sum s f).toH1Function.toFun =
      (fun x => ∑ i ∈ s, (f i).toH1Function x) :=
  (old_hessian_h10_sum_exists s f).choose_spec.1

theorem old_hessian_h10_sum_grad {ι : Type*} {U : Set (Vec 2)}
    (s : Finset ι) (f : ι → H10Function U) :
    (oldHessianH10Sum s f).toH1Function.grad =
      (fun x => ∑ i ∈ s, (f i).toH1Function.grad x) :=
  (old_hessian_h10_sum_exists s f).choose_spec.2

/-- The coarse cell-zero first potential, in the fixed physical frame and
on the literal completed coefficient. The coarse depth remains explicit. -/
def oldHessianCoarsePotential (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) : H10Function (openCubeSet Q) := by
  classical
  let F : Vec 2 → BlockVec 2 := fun _ => (0,e)
  let hF : MemBlockL2 (openCubeSet Q) F := memLp_const (0,e)
  let phi (R : {R : TriadicCube 2 // R ∈ descendantsAtDepth Q depth}) :=
    oldSignedCellFirstCorrector Q R.1 (openCubeSet_subset_of_mem_descendantsAtDepth R.2)
      nu sigma hnu hsigma k F hF
  exact oldHessianH10Sum Finset.univ (fun R => (phi R).extendByZeroToOpenSuperset
    (measurableSet_openCubeSet R.1) (isOpen_openCubeSet Q)
    (openCubeSet_subset_of_mem_descendantsAtDepth R.2))

/-- The glued coarse potential differentiates to exactly the first component
of the actual coarse bottom-load residual, including the cell-zero gauges. -/
theorem old_hessian_coarse_potential_grad (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    (oldHessianCoarsePotential Q depth nu sigma hnu hsigma k e).toH1Function.grad =
      (fun x => (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (fun _ => (0,e)) (memLp_const (0,e)) x).1) := by
  classical
  unfold oldHessianCoarsePotential
  rw [old_hessian_h10_sum_grad]
  funext x
  simp only [oldSignedLocalResidual,Prod.fst_sum]
  apply Finset.sum_congr rfl
  intro R _
  rw [H10Function.extendByZeroToOpenSuperset_grad]
  by_cases hx : x ∈ openCubeSet R.1
  · simp [H10Function.zeroExtensionGrad,hx,old_signed_cell_first_corrector_grad]
  · simp [H10Function.zeroExtensionGrad,hx]

/-- On each actual coarse cell the glued potential is literally the genuine
zero-trace cell corrector. This retains its cell-zero gauge for product bounds. -/
theorem old_hessian_coarse_potential_cell (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2)
    (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q depth) (x : Vec 2) (hx : x ∈ openCubeSet R) :
    (oldHessianCoarsePotential Q depth nu sigma hnu hsigma k e).toH1Function x =
    (oldSignedCellFirstCorrector Q R (openCubeSet_subset_of_mem_descendantsAtDepth hR)
      nu sigma hnu hsigma k (fun _ => (0,e)) (memLp_const (0,e))).toH1Function x := by
  classical
  unfold oldHessianCoarsePotential
  rw [old_hessian_h10_sum_fun]
  dsimp only
  rw [Fintype.sum_eq_single ⟨R,hR⟩]
  · simp [H10Function.zeroExtension,hx]
  · intro S hne
    have hSR : S.1 ≠ R := fun heq => hne (Subtype.ext heq)
    have hd := pairwiseDisjoint_openCubeSet_descendantsAtDepth Q depth S.2 hR hSR
    have hxS : x ∉ openCubeSet S.1 := fun hxs => (Set.disjoint_left.mp hd) hxs hx
    simp [H10Function.zeroExtension,hxS]

end
end ASDExplicitGamma.Scalar
