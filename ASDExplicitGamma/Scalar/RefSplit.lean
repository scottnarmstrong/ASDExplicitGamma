module

public import ASDExplicitGamma.Scalar.RefFinal
public import ASDExplicitGamma.Scalar.PairLamSplit
public import ASDExplicitGamma.Scalar.DefectT4Interface

/-! Successor of the forced/inner split of the defect budget (corrected reference). -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

namespace Cfg''

variable (C : Cfg'')

/-- The forcedR part `B_old C_{H_j} (e,0) − σ(0, F H_j)` of the defect of mode `j`. -/
def forcedR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) : C.Pr :=
  delta' C.Vm C.FlR (C.Bop old) C.load C.σ (C.Hs j)

/-- The tiled depth-134 weak energies of the two components of the forcedR parts, `j < n`. -/
def forcedLamR (n : ℕ) (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) : ℝ :=
  ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134
      (rep'' C.nQ (potMap C.Q ((C.forcedR old j).ofLp.2 : HilbertVectorL2
        (openCubeSet C.Q)))).toH1Function.grad +
    ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.forcedR old j).ofLp.1).1

theorem deltaR_eq_forced_add_inner (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ) :
    C.deltaR old j = C.forcedR old j + C.inner old j := by
  unfold deltaR forcedR inner
  rw [delta_apply', delta_apply']
  simp only [map_sub]
  abel

theorem lam_splitR (n : ℕ) (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) :
    Real.sqrt (C.LamFR n old + C.LamGR n old) ≤
      Real.sqrt (C.forcedLamR n old) + Real.sqrt (C.innerLam n old) := by
  classical
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  let rx : C.Pr → Vec 2 → Vec 2 := fun z =>
    (rep'' C.nQ (potMap C.Q ((z.ofLp.2 : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad
  let ry : C.Pr → Vec 2 → Vec 2 := fun z => (rep2 C.nQ 134 z.ofLp.1).1
  have mrx : ∀ z, MemVectorL2 (openCubeSet C.Q) (rx z) := fun z =>
    (rep'' C.nQ _).toH1Function.grad_memVectorL2
  have mry : ∀ z, MemVectorL2 (openCubeSet C.Q) (ry z) := fun z => rep_memL2 _
  have hrx : ∀ z z' : C.Pr, toHilbertVectorL2OfVecField (mrx (z + z')) =
      toHilbertVectorL2OfVecField (mrx z) + toHilbertVectorL2OfVecField (mrx z') := by
    intro z z'
    change (rep'' C.nQ _).toH1Function.gradToHilbertVectorL2 =
      (rep'' C.nQ _).toH1Function.gradToHilbertVectorL2 +
        (rep'' C.nQ _).toH1Function.gradToHilbertVectorL2
    rw [rep_class, rep_class, rep_class, potMap_gradient, potMap_gradient, potMap_gradient]
    rfl
  have hry : ∀ z z' : C.Pr, toHilbertVectorL2OfVecField (mry (z + z')) =
      toHilbertVectorL2OfVecField (mry z) + toHilbertVectorL2OfVecField (mry z') := by
    intro z z'
    change toHilbertVectorL2OfVecField (rep_memL2 _) = toHilbertVectorL2OfVecField (rep_memL2 _) +
      toHilbertVectorL2OfVecField (rep_memL2 _)
    rw [hilbert_rebuild, hilbert_rebuild, hilbert_rebuild]
    rfl
  have h := sum_split C.Q (J := n) (fun j => rx (C.forcedR old j)) (fun j => rx (C.inner old j))
    (fun j => rx (C.deltaR old j)) (fun j => ry (C.forcedR old j)) (fun j => ry (C.inner old j))
    (fun j => ry (C.deltaR old j)) (fun j => mrx _) (fun j => mrx _) (fun j => mry _)
    (fun j => mry _)
    (fun j => ae_add_of_classes (mrx _) (mrx _) (mrx _) (by
      rw [C.deltaR_eq_forced_add_inner old j]; exact hrx _ _))
    (fun j => ae_add_of_classes (mry _) (mry _) (mry _) (by
      rw [C.deltaR_eq_forced_add_inner old j]; exact hry _ _))
  exact h


end Cfg''

end

end ASDExplicitGamma.Scalar
