module

public import ASDExplicitGamma.Scalar.OldHessianTrialBrokenPairing
public import ASDExplicitGamma.Scalar.OldHessianTrialNodalDuality

/-! The unchanged fine nodal interpolant against varying local receivers. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Complete nodal K/P contraction with independent physical receiver
fields on each fine cell. Every source positive-series premise is supplied
by the genuine zero-trace nodal interpolant. -/
theorem old_hessian_nodal_broken_pairing (Q : TriadicCube 2) (fine : ℕ)
    (u : Fin 2 → H10Function (openCubeSet Q))
    (G : OldSignedCellIndex Q fine → Fin 2 → Vec 2 → Vec 2)
    (hG : ∀ U i k,MemLp (fun x => G U i x k) 2 (normalizedCubeMeasure U.val)) :
    |oldSignedCellAverage Q fine (fun U => ∑ i : Fin 2,cubeAverage U.val
      (fun x => vecDot (G U i x) ((diagInterpolant Q fine (u i).toH1Function).grad x)))|≤
      Real.sqrt (∑ i : Fin 2,lemmaVTiledWeakEnergy Q fine (u i).toH1Function.grad)*
        Real.sqrt (∑ i : Fin 2,oldSignedCellAverage Q fine (fun U => vectorWeakHaarEnergy U.val (G U i))) := by
  let F := fun (_U : OldSignedCellIndex Q fine) (i : Fin 2) =>
    (diagInterpolant Q fine (u i).toH1Function).grad
  have hF (U : OldSignedCellIndex Q fine) (i k : Fin 2) :
      MemLp (fun x => F U i x k) 2 (normalizedCubeMeasure U.val) :=
    hilbert_memLp_descendant U.property
      ((diagInterpolant Q fine (u i).toH1Function).grad_memL2_normalizedCubeMeasure k)
  have hpos (U : OldSignedCellIndex Q fine) (i k : Fin 2) :=
    old_hessian_nodal_gradient_positive Q fine (u i) U.val U.property k
  have hh := old_hessian_broken_load_pairing Q fine G F hG hF hpos
  have hp (i : Fin 2) : oldSignedCellAverage Q fine (fun U => vectorPositiveHaarEnergy U.val (F U i))≤
      lemmaVTiledWeakEnergy Q fine (u i).toH1Function.grad := by
    rw [old_signed_cell_average_eq_descendantsAverage Q fine (fun U =>
      vectorPositiveHaarEnergy U (diagInterpolant Q fine (u i).toH1Function).grad)]
    exact diagInterpolant_h10_gradient_energy_le Q fine (u i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  exact hh.trans ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsum) (Real.sqrt_nonneg _)).trans_eq (by ring))

end
end ASDExplicitGamma.Scalar
