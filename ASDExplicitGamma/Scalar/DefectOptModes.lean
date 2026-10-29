module

public import ASDExplicitGamma.Scalar.DefectPosHaarFields

/-! Zero-padded mode families: the row/column sum bound when some indices carry no mode. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian
open scoped BigOperators

noncomputable section

theorem tiledPositiveEnergy_zero (Q : TriadicCube 2) (m : ℕ) :
    tiledPositiveEnergy Q m 0 = 0 := by
  refine tendsto_nhds_unique (tiledPartialForm_tendsto Q m 0) ?_
  have : ∀ N, (tiledPartialForm Q m N).form 0 0 = 0 := fun N => by simp
  simp only [this]
  exact tendsto_const_nhds

/-- A mode that may be absent (then the source field is zero). -/
def rowEltOpt (Q : TriadicCube 2) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (o : Option whiteBasisIndex) (r : H10Function (openCubeSet Q)) : TiledHaarField Q m :=
  match o with
  | none => 0
  | some l => rowElt Q m b L l r

theorem defect_rowcol_sum_le_opt (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})
    {n : ℕ} (e : Fin n → Option whiteBasisIndex)
    (he : ∀ i j l, e i = some l → e j = some l → i = j)
    (d : Fin n → H10Function (openCubeSet (originCube 2 nQ))) :
    let B : Fin n → Fin n → TiledHaarField (originCube 2 nQ) m := fun i j =>
      rowEltOpt (originCube 2 nQ) m b L (e i) (d j)
    tiledPositiveEnergy (originCube 2 nQ) m (∑ i, B i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy (originCube 2 nQ) m (B i j) ≤
      3 * colKappa (originCube 2 nQ) m b L ^ 2 *
        ∑ j, lemmaVTiledWeakEnergy (originCube 2 nQ) m (d j).toH1Function.grad := by
  classical
  intro B
  set κc := colKappa (originCube 2 nQ) m b L
  let V : Finset (Fin n) := Finset.univ.filter fun i => (e i).isSome
  let g : V → whiteBasisIndex := fun i => (e i.1).get (Finset.mem_filter.mp i.2).2
  have hg : ∀ i : V, e i.1 = some (g i) := fun i => by
    have h : (e i.1).isSome := (Finset.mem_filter.mp i.2).2
    simp [g]
  have hginj : Function.Injective g := by
    intro i j hij
    exact Subtype.ext (he i.1 j.1 (g i) (hg i) (by rw [hij]; exact hg j))
  have hBopt : ∀ i j, B i j = if h : (e i).isSome then
      rowElt (originCube 2 nQ) m b L ((e i).get h) (d j) else 0 := by
    intro i j
    cases hei : e i with
    | none => simp [B, rowEltOpt, hei]
    | some l => simp [B, rowEltOpt, hei]
  have hzero : ∀ i, e i = none → ∀ j, B i j = 0 := fun i hi j => by simp [B, rowEltOpt, hi]
  have hW : 0 ≤ ∑ j, lemmaVTiledWeakEnergy (originCube 2 nQ) m (d j).toH1Function.grad :=
    Finset.sum_nonneg fun j _ => lemmaVTiledWeakEnergy_nonneg _ m _
  -- diagonal
  have hdiag : (∑ i, B i i) = ∑ i : V, rowElt (originCube 2 nQ) m b L (g i) (d i.1) := by
    have h1 : (∑ i, B i i) = ∑ i ∈ V, B i i := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      have : e i = none := by simpa [V] using hi
      exact hzero i this i
    rw [h1, ← Finset.sum_coe_sort V]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [B, rowEltOpt, hg i]
  have hrow := rowElt_diag_sum_bound (originCube 2 nQ) m b L g hginj (fun i : V => d i.1)
  have hk := rowKappa_le_ColKappa (originCube 2 nQ) m b L
  have hk0 : 0 ≤ rowKappa (originCube 2 nQ) m b L := by
    unfold rowKappa
    have := (diagMeshRadius_pos (originCube 2 nQ) m).le
    positivity
  have hkk : rowKappa (originCube 2 nQ) m b L ^ 2 ≤ κc ^ 2 := pow_le_pow_left₀ hk0 hk 2
  have hsub : ∑ i : V, lemmaVTiledWeakEnergy (originCube 2 nQ) m (d i.1).toH1Function.grad ≤
      ∑ j, lemmaVTiledWeakEnergy (originCube 2 nQ) m (d j).toH1Function.grad := by
    rw [Finset.sum_coe_sort V (fun i => lemmaVTiledWeakEnergy (originCube 2 nQ) m
      (d i).toH1Function.grad)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => lemmaVTiledWeakEnergy_nonneg _ m _)
  have hdiagb : tiledPositiveEnergy (originCube 2 nQ) m (∑ i, B i i) ≤
      κc ^ 2 * ∑ j, lemmaVTiledWeakEnergy (originCube 2 nQ) m (d j).toH1Function.grad := by
    rw [hdiag]
    calc _ ≤ rowKappa (originCube 2 nQ) m b L ^ 2 *
          ∑ i : V, lemmaVTiledWeakEnergy (originCube 2 nQ) m (d i.1).toH1Function.grad := hrow
      _ ≤ κc ^ 2 * ∑ i : V, lemmaVTiledWeakEnergy (originCube 2 nQ) m (d i.1).toH1Function.grad :=
          mul_le_mul_of_nonneg_right hkk (Finset.sum_nonneg fun _ _ =>
            lemmaVTiledWeakEnergy_nonneg _ m _)
      _ ≤ _ := mul_le_mul_of_nonneg_left hsub (sq_nonneg _)
  -- columns
  have hcol : ∀ j, ∑ i, tiledPositiveEnergy (originCube 2 nQ) m (B i j) ≤
      κc ^ 2 * lemmaVTiledWeakEnergy (originCube 2 nQ) m (d j).toH1Function.grad := by
    intro j
    have h := rowElt_column_bound nQ m b L (Finset.univ.image g) (d j)
    rw [Finset.sum_image (fun i _ i' _ hii => hginj hii)] at h
    have h1 : (∑ i, tiledPositiveEnergy (originCube 2 nQ) m (B i j)) =
        ∑ i ∈ V, tiledPositiveEnergy (originCube 2 nQ) m (B i j) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      have : e i = none := by simpa [V] using hi
      rw [hzero i this j, tiledPositiveEnergy_zero]
    rw [h1, ← Finset.sum_coe_sort V]
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [B, rowEltOpt, hg i]
  have hcolsum : ∑ i, ∑ j, tiledPositiveEnergy (originCube 2 nQ) m (B i j) ≤
      κc ^ 2 * ∑ j, lemmaVTiledWeakEnergy (originCube 2 nQ) m (d j).toH1Function.grad := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hcol j
  linarith

end

end ASDExplicitGamma.Scalar
