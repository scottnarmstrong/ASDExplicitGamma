module

public import ASDExplicitGamma.Scalar.GSlotMain
public import ASDExplicitGamma.Scalar.DefectHMeas

/-! Symmetrized potential-slot rows and their Wick bound `3 κ² ∑ W(g_j)`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian
open scoped BigOperators Topology InnerProductSpace ENNReal

noncomputable section

variable (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})

local notation "QQ" => originCube 2 nQ

/-- A possibly absent mode (then zero). -/
def gSlotOpt (o : Option whiteBasisIndex) (g : TiledL2Field QQ m) : TiledHaarField QQ m :=
  match o with
  | none => 0
  | some l => gSlot nQ m b L l g

/-- Symmetrized potential-slot rows. -/
def gSymRows {n : ℕ} (e : Fin n → Option whiteBasisIndex)
    (g : Fin n → TiledL2Field QQ m) : Fin n → Fin n → TiledHaarField QQ m := fun i j =>
  (1 / 2 : ℝ) • (gSlotOpt nQ m b L (e i) (g j) + gSlotOpt nQ m b L (e j) (g i))

theorem gSymRows_symm {n : ℕ} (e : Fin n → Option whiteBasisIndex)
    (g : Fin n → TiledL2Field QQ m) (i j : Fin n) :
    gSymRows nQ m b L e g i j = gSymRows nQ m b L e g j i := by
  unfold gSymRows; rw [add_comm]

theorem gSymRows_diag {n : ℕ} (e : Fin n → Option whiteBasisIndex)
    (g : Fin n → TiledL2Field QQ m) (i : Fin n) :
    gSymRows nQ m b L e g i i = gSlotOpt nQ m b L (e i) (g i) := by
  unfold gSymRows
  rw [← two_smul ℝ, smul_smul]; norm_num

theorem psdDefectSource_gsymRows {n : ℕ} (e : Fin n → Option whiteBasisIndex)
    (g : Fin n → TiledL2Field QQ m) (x : Fin n → ℝ) :
    psdDefectSource (gSymRows nQ m b L e g) x =
      psdDefectSource (fun i j => gSlotOpt nQ m b L (e i) (g j)) x := by
  unfold psdDefectSource gSymRows
  simp only [smul_add, Finset.sum_add_distrib, smul_smul]
  have h : ∑ i : Fin n, ∑ j : Fin n, (x i * x j * (1 / 2 : ℝ)) • gSlotOpt nQ m b L (e j) (g i) =
      ∑ i : Fin n, ∑ j : Fin n, (x i * x j * (1 / 2 : ℝ)) • gSlotOpt nQ m b L (e i) (g j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (x j) (x i)]
  rw [h, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← add_smul]; congr 1; ring

theorem gslot_rowcol_opt {n : ℕ} (e : Fin n → Option whiteBasisIndex)
    (he : ∀ i j l, e i = some l → e j = some l → i = j)
    (g : Fin n → TiledL2Field QQ m) :
    let B : Fin n → Fin n → TiledHaarField QQ m := fun i j => gSlotOpt nQ m b L (e i) (g j)
    tiledPositiveEnergy QQ m (∑ i, B i i) + 2 * ∑ i, ∑ j, tiledPositiveEnergy QQ m (B i j) ≤
      3 * colKappa QQ m b L ^ 2 * ∑ j, lemmaVTiledWeakEnergy QQ m (g j).1 := by
  classical
  intro B
  set κc := colKappa QQ m b L
  let V : Finset (Fin n) := Finset.univ.filter fun i => (e i).isSome
  let gi : V → whiteBasisIndex := fun i => (e i.1).get (Finset.mem_filter.mp i.2).2
  have hg : ∀ i : V, e i.1 = some (gi i) := fun i => by
    have h : (e i.1).isSome := (Finset.mem_filter.mp i.2).2
    simp [gi]
  have hginj : Function.Injective gi := by
    intro i j hij
    exact Subtype.ext (he i.1 j.1 (gi i) (hg i) (by rw [hij]; exact hg j))
  have hzero : ∀ i, e i = none → ∀ j, B i j = 0 := fun i hi j => by simp [B, gSlotOpt, hi]
  have hW0 : ∀ j, 0 ≤ lemmaVTiledWeakEnergy QQ m (g j).1 :=
    fun j => lemmaVTiledWeakEnergy_nonneg _ m _
  have hk0 := rowKappa_nonneg nQ m b L
  have hkk : rowKappa QQ m b L ^ 2 ≤ κc ^ 2 :=
    pow_le_pow_left₀ hk0 (rowKappa_le_ColKappa QQ m b L) 2
  -- diagonal
  let z : whiteBasisIndex → TiledL2Field QQ m := fun l =>
    if h : ∃ i : V, gi i = l then g (h.choose).1 else 0
  have hz : ∀ i : V, z (gi i) = g i.1 := by
    intro i
    have h : ∃ j : V, gi j = gi i := ⟨i, rfl⟩
    simp only [z, dif_pos h]
    rw [hginj h.choose_spec]
  have hdiag : (∑ i, B i i) = ∑ i : V, gSlot nQ m b L (gi i) (z (gi i)) := by
    have h1 : (∑ i, B i i) = ∑ i ∈ V, B i i := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      exact hzero i (by simpa [V] using hi) i
    rw [h1, ← Finset.sum_coe_sort V]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hz i]; simp [B, gSlotOpt, hg i]
  have hrow := gSlot_row nQ m b L (Finset.univ.image gi) z
  rw [Finset.sum_image (fun i _ j _ hij => hginj hij)] at hrow
  have himg : ∑ l ∈ Finset.univ.image gi, lemmaVTiledWeakEnergy QQ m (z l).1 =
      ∑ i : V, lemmaVTiledWeakEnergy QQ m (z (gi i)).1 :=
    Finset.sum_image (fun i _ j _ hij => hginj hij)
  rw [himg] at hrow
  have hrow' : ∑ i : V, lemmaVTiledWeakEnergy QQ m (z (gi i)).1 =
      ∑ i : V, lemmaVTiledWeakEnergy QQ m (g i.1).1 :=
    Finset.sum_congr rfl fun i _ => by rw [hz i]
  have hsub : ∑ i : V, lemmaVTiledWeakEnergy QQ m (g i.1).1 ≤
      ∑ j, lemmaVTiledWeakEnergy QQ m (g j).1 := by
    rw [Finset.sum_coe_sort V (fun i => lemmaVTiledWeakEnergy QQ m (g i).1)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hW0 j)
  have hdiagb : tiledPositiveEnergy QQ m (∑ i, B i i) ≤ κc ^ 2 * ∑ j, lemmaVTiledWeakEnergy QQ m (g j).1 := by
    rw [hdiag]
    calc _ ≤ κc ^ 2 * ∑ i : V, lemmaVTiledWeakEnergy QQ m (z (gi i)).1 := hrow
      _ ≤ _ := by rw [hrow']; exact mul_le_mul_of_nonneg_left hsub (sq_nonneg _)
  -- columns
  have hcol : ∀ j, ∑ i, tiledPositiveEnergy QQ m (B i j) ≤
      κc ^ 2 * lemmaVTiledWeakEnergy QQ m (g j).1 := by
    intro j
    have h := gSlot_col nQ m b L (Finset.univ.image gi) (g j)
    rw [Finset.sum_image (fun i _ i' _ hii => hginj hii)] at h
    have h1 : (∑ i, tiledPositiveEnergy QQ m (B i j)) =
        ∑ i ∈ V, tiledPositiveEnergy QQ m (B i j) := by
      symm
      refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
      rw [hzero i (by simpa [V] using hi) j, tiledPositiveEnergy_zero]
    rw [h1, ← Finset.sum_coe_sort V]
    have h2 : ∑ i : V, tiledPositiveEnergy QQ m (B i.1 j) =
        ∑ i : V, tiledPositiveEnergy QQ m (gSlot nQ m b L (gi i) (g j)) :=
      Finset.sum_congr rfl fun i _ => by simp only [B, gSlotOpt, hg i]
    rw [h2]
    exact h.trans (mul_le_mul_of_nonneg_right hkk (hW0 j))
  have hcolsum : ∑ i, ∑ j, tiledPositiveEnergy QQ m (B i j) ≤
      κc ^ 2 * ∑ j, lemmaVTiledWeakEnergy QQ m (g j).1 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hcol j
  linarith

theorem gsymRows_wick {n : ℕ} (e : Fin n → Option whiteBasisIndex)
    (he : ∀ i j l, e i = some l → e j = some l → i = j)
    (g : Fin n → TiledL2Field QQ m) :
    tiledPositiveEnergy QQ m (∑ i, gSymRows nQ m b L e g i i) +
        2 * ∑ i, ∑ j, tiledPositiveEnergy QQ m (gSymRows nQ m b L e g i j) ≤
      3 * colKappa QQ m b L ^ 2 * ∑ j, lemmaVTiledWeakEnergy QQ m (g j).1 := by
  have h := gslot_rowcol_opt nQ m b L e he g
  dsimp only at h
  have hdiag : ∑ i, gSymRows nQ m b L e g i i = ∑ i, gSlotOpt nQ m b L (e i) (g i) :=
    Finset.sum_congr rfl fun i _ => gSymRows_diag nQ m b L e g i
  rw [hdiag]
  have hoff : ∑ i, ∑ j, tiledPositiveEnergy QQ m (gSymRows nQ m b L e g i j) ≤
      ∑ i, ∑ j, tiledPositiveEnergy QQ m (gSlotOpt nQ m b L (e i) (g j)) := by
    calc _ ≤ ∑ i, ∑ j, ((tiledPositiveEnergy QQ m (gSlotOpt nQ m b L (e i) (g j)) +
          tiledPositiveEnergy QQ m (gSlotOpt nQ m b L (e j) (g i))) / 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => tpe_half_add_le _ m _ _
      _ = _ := by
          simp only [add_div, Finset.sum_add_distrib]
          rw [Finset.sum_comm (f := fun i j => tiledPositiveEnergy QQ m
            (gSlotOpt nQ m b L (e j) (g i)) / 2)]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  linarith

end

end ASDExplicitGamma.Scalar
