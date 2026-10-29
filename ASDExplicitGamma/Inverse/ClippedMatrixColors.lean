module

public import ASDExplicitGamma.Inverse.ClippedMatrixConditional
public import ASDExplicitGamma.Inverse.RestrictionLocalSigma
public import Mathlib.Data.Int.ModEq

/-! Literal (4*3^40)^2 source colors for full old clipped cells. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ProbabilityTheory Algsuperdiff.Section3

/-- The source palette; coordinates are reduced modulo 4*3^40 fine lengths. -/
abbrev ClippedCellColor := Fin 2 → Fin (4*3^40)

def clippedCellColor (Q : TriadicCube 2) : ClippedCellColor := fun d =>
  ⟨(Q.index d%((4*3^40:ℕ):ℤ)).toNat,by
    have hp : (0:ℤ) < ((4*3^40:ℕ):ℤ) := by positivity
    have hl := Int.emod_nonneg (Q.index d) hp.ne'
    have hu := Int.emod_lt_of_pos (Q.index d) hp
    omega⟩

theorem clipped_cell_color_card : Fintype.card ClippedCellColor=(4*3^40)^2 := by
  simp only [ClippedCellColor,Fintype.card_fun,Fintype.card_fin]

/-- Same-color distinct cells of the same scale have the literal source gap. -/
theorem clipped_cell_color_index_gap (Q R : TriadicCube 2) (hs : Q.scale=R.scale) (hne : Q≠R)
    (hc : clippedCellColor Q=clippedCellColor R) :
    ∃ d, (4*3^40:ℤ) ≤ |R.index d-Q.index d| := by
  have hi : Q.index≠R.index := by
    intro h
    apply hne
    cases Q
    cases R
    cases hs
    cases h
    rfl
  obtain ⟨d,hd⟩ : ∃ d, Q.index d≠R.index d := by
    by_contra! h
    exact hi (funext h)
  have hc' := congrArg Fin.val (congrFun hc d)
  change (Q.index d%((4*3^40:ℕ):ℤ)).toNat=(R.index d%((4*3^40:ℕ):ℤ)).toNat at hc'
  have hp : (0:ℤ) < ((4*3^40:ℕ):ℤ) := by positivity
  have h0 := Int.emod_nonneg (Q.index d) hp.ne'
  have h1 := Int.emod_nonneg (R.index d) hp.ne'
  have hrem : Q.index d%((4*3^40:ℕ):ℤ)=R.index d%((4*3^40:ℕ):ℤ) := by omega
  have hmod : Int.ModEq ((4*3^40:ℕ):ℤ) (Q.index d) (R.index d) := hrem
  exact ⟨d,by exact_mod_cast Int.le_abs_of_dvd (sub_ne_zero.mpr hd.symm) hmod.dvd⟩

/-- Sharp coordinate-range separation of the whole actual physical cells. -/
theorem clipped_cell_color_separation (Q R : TriadicCube 2) (hs : Q.scale=R.scale) (hne : Q≠R)
    (hc : clippedCellColor Q=clippedCellColor R) {x y : Vec 2} (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet R) :
    ∃ d : Fin 2, (3:ℝ)^(Q.scale+40) ≤ |(x-y) d| := by
  obtain ⟨d,hd⟩ := clipped_cell_color_index_gap Q R hs hne hc
  have hdelta : (4*3^40:ℝ) ≤ |(R.index d:ℝ)-(Q.index d:ℝ)| := by exact_mod_cast hd
  have hxs := hx d
  have hys := hy d
  change ((Q.index d:ℝ)-1/2)*(3:ℝ)^Q.scale ≤ x d ∧ x d < ((Q.index d:ℝ)+1/2)*(3:ℝ)^Q.scale at hxs
  change ((R.index d:ℝ)-1/2)*(3:ℝ)^R.scale ≤ y d ∧ y d < ((R.index d:ℝ)+1/2)*(3:ℝ)^R.scale at hys
  rw [← hs] at hys
  have hside : 0 ≤ (3:ℝ)^Q.scale := (zpow_pos (by norm_num) _).le
  have hgap := mul_le_mul_of_nonneg_right hdelta hside
  have hbase : (3:ℝ)^(Q.scale+40)=(3:ℝ)^Q.scale*(3:ℝ)^40 := by
    rw [zpow_add₀ (by norm_num : (3:ℝ)≠0),zpow_ofNat]
  refine ⟨d,?_⟩
  rw [hbase]
  change _ ≤ |x d-y d|
  rcases le_total 0 ((R.index d:ℝ)-(Q.index d:ℝ)) with hpos | hneg
  · rw [abs_of_nonneg hpos] at hgap
    have hlo : (3:ℝ)^Q.scale*(3:ℝ)^40 ≤ y d-x d := by
      nlinarith only [hgap,hxs.2,hys.1,hside]
    exact hlo.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · rw [abs_of_nonpos hneg] at hgap
    have hlo : (3:ℝ)^Q.scale*(3:ℝ)^40 ≤ x d-y d := by
      nlinarith only [hgap,hxs.1,hys.2,hside]
    exact hlo.trans (le_abs_self _)

/-- Joint independence inside each literal source color; full history and
all lower shells remain in the observed sigma-fields. -/
theorem clipped_cell_matrices_colored_independent {I : Type*}
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (j : ℤ) (τ : ℝ)
    (Q : I → TriadicCube 2) (hs : ∀ i, (Q i).scale=j) (hinj : Function.Injective Q) (c : ClippedCellColor) :
    iIndepFun (fun i : {i // clippedCellColor (Q i)=c} => clippedCellMatrix M (j+40) (Q i.1) τ)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  apply restriction_local_observables_independent M h hM (j+40)
    (fun i : {i // clippedCellColor (Q i)=c} => cubeSet (Q i.1))
    (fun i => measurableSet_cubeSet _)
  · intro i k hik x hx y hy
    have hne : Q i.val≠Q k.val := fun he => hik (Subtype.ext (hinj he))
    have hsame : (Q i.val).scale=(Q k.val).scale := (hs i.val).trans (hs k.val).symm
    have hcol : clippedCellColor (Q i.val)=clippedCellColor (Q k.val) := i.property.trans k.property.symm
    simpa only [hs i.val] using clipped_cell_color_separation _ _ hsame hne hcol hx hy
  · intro i
    exact clipped_cell_matrix_local_measurable M (j+40) (Q i.val) τ Set.Subset.rfl

end ASDExplicitGamma.Inverse
