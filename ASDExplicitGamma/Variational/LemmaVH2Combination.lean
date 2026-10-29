module

public import ASDExplicitGamma.Variational.LemmaVH2Row
public import ASDExplicitGamma.Triadic.PlanarDirectionLinear

/-! The lifted row commutes with genuine finite combinations of directions. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

 theorem lemmaVRowCombination_linearCombination {Q : TriadicCube 2} {ι : Type*}
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η : ι → PlanarW2Infinity Q) (v : H1Function (openCubeSet Q)) (s : Finset ι) (c : ι → ℝ) :
    lemmaVRowCombination I (fun l => (η l).value) v s c =
      lemmaVPlanarRowField I (PlanarW2Infinity.linearCombination η s c).value v := by
  funext x b
  simp only [lemmaVRowCombination, lemmaVPlanarRowField, lemmaVPlanarWeakColumnDivergence,
    PlanarW2Infinity.linearCombination, h1_finset_sum_toFun,
    Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply, smul_eq_mul,
    matVecMul, Response.responsePlanarJ, Fin.sum_univ_two, h1_finset_sum_grad_apply]
  fin_cases b <;> simp <;> simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul, mul_neg, Finset.sum_neg_distrib] <;> ring_nf <;>
    simp only [mul_comm, mul_left_comm, mul_assoc]

end
end ASDExplicitGamma.Variational
