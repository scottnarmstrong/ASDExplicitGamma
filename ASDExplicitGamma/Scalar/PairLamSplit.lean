module

public import ASDExplicitGamma.Scalar.PairSplit

/-! The weak budget `LamF + LamG` of the first-response defect splits, with constant one, into
the forced budget and the inner budget. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open scoped BigOperators

noncomputable section

theorem ae_add_of_classes {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    {f g h : Vec 2 → Vec 2} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) (hh : MemVectorL2 U h)
    (hcl : toHilbertVectorL2OfVecField hh =
      toHilbertVectorL2OfVecField hf + toHilbertVectorL2OfVecField hg) :
    h =ᵐ[volumeMeasureOn U] fun x i => f x i + g x i := by
  have hsum : MemVectorL2 U (fun x i => f x i + g x i) := hf.add hg
  apply ae_of_toHilbert_eq hh hsum
  rw [hcl]
  exact (toHilbertVectorL2OfVecField_add hf hg).symm

namespace Cfg''

variable (C : Cfg'')

/-- The inner weak budget `Σ_j [W(inner_x) + W(inner_y)]`. -/
def innerLam (n : ℕ) (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) : ℝ :=
  ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134
      (rep'' C.nQ (potMap C.Q ((C.inner old j).ofLp.2 : HilbertVectorL2
        (openCubeSet C.Q)))).toH1Function.grad +
    ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.inner old j).ofLp.1).1

end Cfg''

end

end ASDExplicitGamma.Scalar
