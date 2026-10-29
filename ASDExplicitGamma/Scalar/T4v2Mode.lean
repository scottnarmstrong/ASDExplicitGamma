module

public import ASDExplicitGamma.Scalar.Lambda8Q3ParentOscillation
public import ASDExplicitGamma.Scalar.FlatResolvent
public import ASDExplicitGamma.Scalar.RefCheckDefect
public import ASDExplicitGamma.Scalar.DefectModes

/-! T4 v2, mode matching: the flat source carrier of the `l`-th shell mode is minus the gradient
of the parent mode potential. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian MeasureTheory
open scoped InnerProductSpace

noncomputable section

theorem t4v2_toHilbert_neg {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    {f g : Vec 2 → Vec 2} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g)
    (h : ∀ᵐ x ∂volumeMeasureOn U, g x = -f x) :
    toHilbertVectorL2OfVecField hg = -toHilbertVectorL2OfVecField hf := by
  apply def_vec_ext
  have h1 := hilbertVectorL2ToVectorL2_toHilbertVectorL2 hg
  have h2 := hilbertVectorL2ToVectorL2_toHilbertVectorL2 hf
  rw [map_neg, h1, h2]
  filter_upwards [coeFn_toVectorL2 hg, Lp.coeFn_neg (toVectorL2 hf), coeFn_toVectorL2 hf, h]
    with x a b c d
  rw [a, b]
  simp [c, d]

theorem t4v2_mode_carrier (Q : TriadicCube 2) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hQ : openCubeSet Q ⊆ openRectangle a b c d) (β : ℝ) (L : {l : ℝ // 0 < l}) (e : Vec 2)
    (n : whiteBasisIndex) :
    (lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet Q)
      (lambda8Q3LoadClass (isOpenBoundedConvexDomain_openCubeSet Q).1.measurableSet a b c d hab hcd e
        (q3H3RangeValue a b c d β L (q3H3RangeFactor a b c d β L (whiteBasis n))))) =
      -(lambda8Q3GaussianModeParentPotential Q β L (-(matVecMul responsePlanarJ e)) n
        ).toH1Function.gradToHilbertVectorL2 := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hspec := (lambda8Q3GaussianModeParentPotential_spec Q β L (-(matVecMul responsePlanarJ e)) n).1
  rw [← hspec]
  unfold lambda8DirichletProjection
  rw [← map_neg]
  congr 1
  have hmem := lambda8Q3LoadField_memVectorL2 (isOpenBoundedConvexDomain_openCubeSet Q).1.measurableSet
    a b c d hab hcd e (q3H3RangeValue a b c d β L (q3H3RangeFactor a b c d β L (whiteBasis n)))
  have hmode := lambda8H1ComponentField_memVectorL2
    (fun i => lambda8Q3GaussianModeLoadH1 Q β L (-(matVecMul responsePlanarJ e)) n i)
  have hneg := t4v2_toHilbert_neg hmem hmode (by
    have hU : ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q), x ∈ openCubeSet Q :=
      ae_restrict_of_forall_mem (measurableSet_openCubeSet Q) (fun x hx => hx)
    filter_upwards [hU] with x hx
    have hyr : x ∈ openRectangle a b c d := hQ hx
    ext i
    have hx' : x ∈ closedRectangle a b c d :=
      ⟨Set.Ioo_subset_Icc_self hyr.1, Set.Ioo_subset_Icc_self hyr.2⟩
    have hv := q3H3RangeValue_factor a b c d β hab hcd L (whiteBasis n) ⟨x, hx'⟩
    have hmodei : lambda8H1ComponentField
        (fun i => lambda8Q3GaussianModeLoadH1 Q β L (-(matVecMul responsePlanarJ e)) n i) x i =
        q3Convolution β L h3Zero (whiteBasis n) x * (-(matVecMul responsePlanarJ e)) i := rfl
    rw [hmodei]
    simp only [lambda8Q3LoadField, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    rw [lambda8CovarianceClamp_eq_of_mem a b c d hab hcd hyr, hv]
    change q3Convolution β L h3Zero (whiteBasis n) x * (-(matVecMul responsePlanarJ e)) i =
      -(q3Convolution β L h3Zero (whiteBasis n) x * matVecMul responsePlanarJ e i)
    simp)
  rw [hneg, neg_neg]
  rfl

end

end ASDExplicitGamma.Scalar
