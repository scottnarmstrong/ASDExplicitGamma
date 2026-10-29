module

public import ASDExplicitGamma.Scalar.PairWeakMain
public import ASDExplicitGamma.Scalar.DefectFinalAux

/-! Column bounds for single sources over possibly absent modes, and the transfer of Hilbert
classes to almost-everywhere equality, for the inner weak budget. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open scoped BigOperators InnerProductSpace

noncomputable section

/-- Equal Hilbert classes of two `L²` fields give almost-everywhere equal fields. -/
theorem ae_of_toHilbert_eq {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]
    {f g : Vec 2 → Vec 2} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g)
    (h : toHilbertVectorL2OfVecField hf = toHilbertVectorL2OfVecField hg) :
    f =ᵐ[volumeMeasureOn U] g := by
  have h1 : toVectorL2 hf = toVectorL2 hg := by
    have := congrArg (hilbertVectorL2ToVectorL2 (U := U)) h
    rwa [hilbertVectorL2ToVectorL2_toHilbertVectorL2, hilbertVectorL2ToVectorL2_toHilbertVectorL2]
      at this
  filter_upwards [coeFn_toVectorL2 hf, coeFn_toVectorL2 hg] with x hx hy
  rw [← hx, ← hy, h1]

/-- Column bound of the flux slot for a single potential over distinct possibly absent modes. -/
theorem rowOpt_col (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l}) {n : ℕ}
    (e : Fin n → Option whiteBasisIndex)
    (he : ∀ i j l, e i = some l → e j = some l → i = j)
    (r : H10Function (openCubeSet (originCube 2 nQ))) :
    ∑ i : Fin n, tiledPositiveEnergy (originCube 2 nQ) m
        (rowEltOpt (originCube 2 nQ) m b L (e i) r) ≤
      colKappa (originCube 2 nQ) m b L ^ 2 *
        lemmaVTiledWeakEnergy (originCube 2 nQ) m r.toH1Function.grad := by
  classical
  let V : Finset (Fin n) := Finset.univ.filter fun i => (e i).isSome
  let g : V → whiteBasisIndex := fun i => (e i.1).get (Finset.mem_filter.mp i.2).2
  have hg : ∀ i : V, e i.1 = some (g i) := fun i => by
    have h : (e i.1).isSome := (Finset.mem_filter.mp i.2).2
    simp [g]
  have hginj : Function.Injective g := by
    intro i j hij
    exact Subtype.ext (he i.1 j.1 (g i) (hg i) (by rw [hij]; exact hg j))
  have h := rowElt_column_bound nQ m b L (Finset.univ.image g) r
  rw [Finset.sum_image (fun i _ i' _ hii => hginj hii)] at h
  have h1 : (∑ i : Fin n, tiledPositiveEnergy (originCube 2 nQ) m
      (rowEltOpt (originCube 2 nQ) m b L (e i) r)) =
      ∑ i ∈ V, tiledPositiveEnergy (originCube 2 nQ) m
        (rowEltOpt (originCube 2 nQ) m b L (e i) r) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    have : e i = none := by simpa [V] using hi
    simp [rowEltOpt, this, tiledPositiveEnergy_zero]
  rw [h1, ← Finset.sum_coe_sort V]
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [rowEltOpt, hg i]

/-- Column bound of the potential slot for a single flux field over distinct modes. -/
theorem gslotOpt_col (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l}) {n : ℕ}
    (e : Fin n → Option whiteBasisIndex)
    (he : ∀ i j l, e i = some l → e j = some l → i = j)
    (g : TiledL2Field (originCube 2 nQ) m) :
    ∑ i : Fin n, tiledPositiveEnergy (originCube 2 nQ) m (gSlotOpt nQ m b L (e i) g) ≤
      colKappa (originCube 2 nQ) m b L ^ 2 *
        lemmaVTiledWeakEnergy (originCube 2 nQ) m g.1 := by
  classical
  let V : Finset (Fin n) := Finset.univ.filter fun i => (e i).isSome
  let gi : V → whiteBasisIndex := fun i => (e i.1).get (Finset.mem_filter.mp i.2).2
  have hg : ∀ i : V, e i.1 = some (gi i) := fun i => by
    have h : (e i.1).isSome := (Finset.mem_filter.mp i.2).2
    simp [gi]
  have hginj : Function.Injective gi := by
    intro i j hij
    exact Subtype.ext (he i.1 j.1 (gi i) (hg i) (by rw [hij]; exact hg j))
  have hk0 := rowKappa_nonneg nQ m b L
  have hkk : rowKappa (originCube 2 nQ) m b L ^ 2 ≤
      colKappa (originCube 2 nQ) m b L ^ 2 :=
    pow_le_pow_left₀ hk0 (rowKappa_le_ColKappa _ m b L) 2
  have h := gSlot_col nQ m b L (Finset.univ.image gi) g
  rw [Finset.sum_image (fun i _ i' _ hii => hginj hii)] at h
  have h1 : (∑ i : Fin n, tiledPositiveEnergy (originCube 2 nQ) m (gSlotOpt nQ m b L (e i) g)) =
      ∑ i ∈ V, tiledPositiveEnergy (originCube 2 nQ) m (gSlotOpt nQ m b L (e i) g) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    have : e i = none := by simpa [V] using hi
    simp [gSlotOpt, this, tiledPositiveEnergy_zero]
  rw [h1, ← Finset.sum_coe_sort V]
  have h2 : ∑ i : V, tiledPositiveEnergy (originCube 2 nQ) m (gSlotOpt nQ m b L (e i.1) g) =
      ∑ i : V, tiledPositiveEnergy (originCube 2 nQ) m (gSlot nQ m b L (gi i) g) :=
    Finset.sum_congr rfl fun i _ => by simp only [gSlotOpt, hg i]
  rw [h2]
  exact h.trans (mul_le_mul_of_nonneg_right hkk (lemmaVTiledWeakEnergy_nonneg _ m _))

end

end ASDExplicitGamma.Scalar
