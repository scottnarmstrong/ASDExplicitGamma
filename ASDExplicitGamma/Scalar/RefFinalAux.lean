module

public import ASDExplicitGamma.Scalar.RefActual

/-! Successor of the Wick bounds, budgets and measurability. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

namespace Cfg''

variable (C : Cfg'')

/-- The flux-slot weak budget `∑_{j<n} W(δx_j)`. -/
def LamFR (n : ℕ) (o : C(closedRectangle C.a C.b C.c C.d, ℝ)) : ℝ :=
  ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134 (rep'' C.nQ (C.zpotR o j)).toH1Function.grad

/-- The potential-slot weak budget `∑_{j<n} W(δy_j)`. -/
def LamGR (n : ℕ) (o : C(closedRectangle C.a C.b C.c C.d, ℝ)) : ℝ :=
  ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.dyR o j)).1

theorem LamFR_nonneg (n : ℕ) (o) : 0 ≤ C.LamFR n o :=
  Finset.sum_nonneg fun j _ => lemmaVTiledWeakEnergy_nonneg _ _ _

theorem LamGR_nonneg (n : ℕ) (o) : 0 ≤ C.LamGR n o :=
  Finset.sum_nonneg fun j _ => lemmaVTiledWeakEnergy_nonneg _ _ _

theorem BFoR_wick (hmesh : diagMeshRadius C.Q 134 ≤ C.L.1 / 729) (old) (n : ℕ) :
    tiledPositiveEnergy C.Q 134 (∑ i, C.BFoR old n i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy C.Q 134 (C.BFoR old n i j) ≤
      3 * defectA ^ 2 * C.amp ^ 2 * C.LamFR n old := by
  have h := symRows_wick C.nQ 134 C.amp C.L (fun i : Fin n => eOpt i) (eOpt_inj_fin n)
    (fun j : Fin n => rep'' C.nQ (C.zpotR old j))
  have hk := colKappa_sq_le C.Q 134 C.amp C.L hmesh
  have hW : 0 ≤ C.LamFR n old := C.LamFR_nonneg n old
  have hdiag : ∑ i, C.BFoR old n i i = -∑ i, symRows C.nQ 134 C.amp C.L
      (fun i : Fin n => eOpt i) (fun j : Fin n => rep'' C.nQ (C.zpotR old j)) i i := by
    unfold BFoR; rw [Finset.sum_neg_distrib]
  rw [hdiag, tiledPositiveEnergy_neg']
  have hoff : ∑ i, ∑ j, tiledPositiveEnergy C.Q 134 (C.BFoR old n i j) =
      ∑ i, ∑ j, tiledPositiveEnergy C.Q 134 (symRows C.nQ 134 C.amp C.L
        (fun i : Fin n => eOpt i) (fun j : Fin n => rep'' C.nQ (C.zpotR old j)) i j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact tiledPositiveEnergy_neg' _ _ _
  rw [hoff]
  refine h.trans ?_
  unfold LamFR
  calc 3 * colKappa C.Q 134 C.amp C.L ^ 2 * ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134
        (rep'' C.nQ (C.zpotR old j)).toH1Function.grad
      ≤ 3 * (defectA ^ 2 * C.amp ^ 2) * ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134
        (rep'' C.nQ (C.zpotR old j)).toH1Function.grad :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) hW
    _ = _ := by ring

theorem BGoR_wick (hmesh : diagMeshRadius C.Q 134 ≤ C.L.1 / 729) (old) (n : ℕ) :
    tiledPositiveEnergy C.Q 134 (∑ i, C.BGoR old n i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy C.Q 134 (C.BGoR old n i j) ≤
      3 * defectA ^ 2 * C.amp ^ 2 * C.LamGR n old := by
  have h := gsymRows_wick C.nQ 134 C.amp C.L (fun i : Fin n => eOpt i) (eOpt_inj_fin n)
    (fun j : Fin n => rep2 C.nQ 134 (C.dyR old j))
  have hk := colKappa_sq_le C.Q 134 C.amp C.L hmesh
  have hW : 0 ≤ C.LamGR n old := C.LamGR_nonneg n old
  refine h.trans ?_
  unfold LamGR
  calc 3 * colKappa C.Q 134 C.amp C.L ^ 2 * ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134
        (rep2 C.nQ 134 (C.dyR old j)).1
      ≤ 3 * (defectA ^ 2 * C.amp ^ 2) * ∑ j : Fin n, lemmaVTiledWeakEnergy C.Q 134
        (rep2 C.nQ 134 (C.dyR old j)).1 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) hW
    _ = _ := by ring


end Cfg''

noncomputable local instance rfH10Measurable (nQ : ℤ) :
    MeasurableSpace (H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) := borel _

noncomputable local instance rfH10Borel (nQ : ℤ) :
    BorelSpace (H10GraphClosedSpace (openCubeSet (originCube 2 nQ))) := ⟨rfl⟩

namespace Cfg''

variable (C : Cfg'')

theorem dyR_continuous (j : ℕ) : Continuous (fun o => C.dyR o j) := by
  have := (WithLp.prodContinuousLinearEquiv 2 ℝ C.Ys C.Xs).continuous.comp (C.deltaR_continuous j)
  exact continuous_fst.comp this

theorem dxR_continuous (j : ℕ) : Continuous (fun o => (C.dxR o j : HilbertVectorL2 (openCubeSet C.Q))) := by
  have := (WithLp.prodContinuousLinearEquiv 2 ℝ C.Ys C.Xs).continuous.comp (C.deltaR_continuous j)
  exact continuous_subtype_val.comp (continuous_snd.comp this)

theorem zpotR_continuous (j : ℕ) : Continuous (fun o => C.zpotR o j) :=
  (potMap C.Q).continuous.comp (C.dxR_continuous j)

theorem LamFR_measurable (n : ℕ) : Measurable (C.LamFR n) := by
  unfold LamFR
  refine Finset.measurable_sum _ fun j _ => ?_
  exact weak_energy_measurable C.nQ 134 (fun o => C.zpotR o j) (C.zpotR_continuous j).measurable

theorem LamGR_measurable (n : ℕ) : Measurable (C.LamGR n) := by
  unfold LamGR
  haveI := openMeasurable C.nQ
  exact gLambda_measurable C.nQ 134 (fun (j : Fin n) o => C.dyR o j)
    (fun j => (C.dyR_continuous j).measurable)

theorem BFoR_meas (n : ℕ) : Measurable (fun p : C(closedRectangle C.a C.b C.c C.d, ℝ) × (ℕ → ℝ) =>
    tiledPositiveEnergy C.Q 134 (psdDefectSource (C.BFoR p.1 n) (fun i : Fin n => p.2 i))) := by
  have h := symDefect_measurable C.nQ 134 C.amp C.L (fun i : Fin n => eOpt i)
    (fun (j : Fin n) o => C.zpotR o j) (fun j => (C.zpotR_continuous j).measurable)
  convert h using 1
  funext p
  unfold BFoR
  rw [psdDefectSource_neg, tiledPositiveEnergy_neg']

theorem BGoR_meas (n : ℕ) : Measurable (fun p : C(closedRectangle C.a C.b C.c C.d, ℝ) × (ℕ → ℝ) =>
    tiledPositiveEnergy C.Q 134 (psdDefectSource (C.BGoR p.1 n) (fun i : Fin n => p.2 i))) := by
  haveI := openMeasurable C.nQ
  exact gsymDefect_measurable C.nQ 134 C.amp C.L (fun i : Fin n => eOpt i)
    (fun (j : Fin n) o => C.dyR o j) (fun j => (C.dyR_continuous j).measurable)

theorem BFoR_symm (old) (n : ℕ) (i j : Fin n) : C.BFoR old n i j = C.BFoR old n j i := by
  unfold BFoR
  rw [symRows_symm]

theorem BGoR_symm (old) (n : ℕ) (i j : Fin n) : C.BGoR old n i j = C.BGoR old n j i := by
  unfold BGoR
  rw [gSymRows_symm]


end Cfg''

end

end ASDExplicitGamma.Scalar
