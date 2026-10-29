module

public import ASDExplicitGamma.Scalar.DualAdmissibility
public import ASDExplicitGamma.Scalar.MolecularCompetitor
public import ASDExplicitGamma.Variational.CubeOpen
public import ASDExplicitGamma.Variational.LocalizedShearMinimum
public import Homogenization.CoarseGraining.HilbertMinimization

/-! Finite compatible cell corrections used by the parent trial. -/
@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory

open ASDExplicitGamma.Variational

/-- A deterministic affine block load viewed as a spatial field. -/
def constantBlockLoad (P : BlockVec 2) : Vec 2 → BlockVec 2 := fun _ => P

/-- Insert finitely many cell corrections into a compatible parent field. -/
noncomputable def compatibleCellPatch {ι : Type*} (X : Vec 2 → BlockVec 2)
    (s : Finset ι) (U : ι → Set (Vec 2)) (Z : ι → Vec 2 → BlockVec 2) :
    Vec 2 → BlockVec 2 := fun x => X x + (∑ i ∈ s, (U i).indicator (Z i - X) x)

/-- The `BlockState` associated with a pointwise block field. -/
def blockStateOfField (X : Vec 2 → BlockVec 2) : BlockState 2 where
  potential := fun x => (X x).1
  flux := fun x => (X x).2

/-- On pairwise disjoint cells, the assembled field agrees with the prescribed
local trial on every inserted cell. -/
theorem compatible_cell_patch_eq_on_cell {ι : Type*} (X : Vec 2 → BlockVec 2)
    (s : Finset ι) (U : ι → Set (Vec 2)) (Z : ι → Vec 2 → BlockVec 2)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (U i) (U j))
    {i : ι} (hi : i ∈ s) {x : Vec 2} (hx : x ∈ U i) :
    compatibleCellPatch X s U Z x = Z i x := by
  classical
  have hsum : (∑ j ∈ s, (U j).indicator (Z j - X) x) =
      (U i).indicator (Z i - X) x := by
    rw [Finset.sum_eq_single i]
    · intro j hj hji
      have hnot : x ∉ U j :=
        (Set.disjoint_left.mp (hdisj i hi j hj (Ne.symm hji))) hx
      simp [hnot]
    · intro hnot
      exact (hnot hi).elim
  rw [compatibleCellPatch]
  rw [hsum]
  simp [hx]

/-- Turn a genuine scalar variation into the ordinary four-clause affine
competitor consumed by `Mu`. -/
def stateOfVariation (P : BlockVec 2) (F : Vec 2 → BlockVec 2) : BlockState 2 :=
  { potential := fun x => P.1 + (F x).1
    flux := fun x => P.2 + (F x).2 }

theorem state_of_variation_admissible (U : Set (Vec 2)) (P : BlockVec 2)
    (F : Vec 2 → BlockVec 2) (hF : ScalarVariation U F) :
    IsBlockMuAdmissible U P (stateOfVariation P F) := by
  change MemVectorL2 U _ ∧ IsPotentialZeroTraceOn U _ ∧
    MemVectorL2 U _ ∧ IsSolenoidalZeroNormalTraceOn U _
  have hp : (fun x => (stateOfVariation P F).potential x - P.1) =
      fun x => (F x).1 := by
    funext x
    simp [stateOfVariation]
  have hq : (fun x => (stateOfVariation P F).flux x - P.2) =
      fun x => (F x).2 := by
    funext x
    simp [stateOfVariation]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp]
    exact memVectorL2_fst_of_memBlockL2 hF.1
  · rw [hp]
    exact hF.2.1
  · rw [hq]
    exact memVectorL2_snd_of_memBlockL2 hF.1
  · rw [hq]
    exact hF.2.2

/-- The parent cell patch is an actual variational competitor for its affine
load, so the source response is bounded by its complete energy. -/
theorem mu_le_cell_patch_trial {Q : TriadicCube 2} {a : CoeffField 2}
    {ν Λ : ℝ} (hEll : IsEllipticFieldOn ν Λ (openCubeSet Q) a)
    (P : BlockVec 2) (F : Vec 2 → BlockVec 2)
    (hF : ScalarVariation (openCubeSet Q) F) :
    Mu (openCubeSet Q) P a ≤
      volumeAverage (openCubeSet Q)
        (fun x => blockEnergyDensity a (stateOfVariation P F) x) := by
  exact Mu_le_competitor (isOpen_openCubeSet Q).measurableSet hEll P
    (stateOfVariation P F) (state_of_variation_admissible _ _ _ hF)

/-- Young's inequality for the squared Euclidean norm, with a selectable
parameter for the high-pass cell-load limit. -/
theorem vecNormSq_add_young (u d : Vec 2) {τ : ℝ} (hτ : 0 < τ) :
    vecNormSq (u + d) ≤ (1 + τ) * vecNormSq u + (1 + τ⁻¹) * vecNormSq d := by
  have hexpand : vecNormSq (u + d) = vecNormSq u + 2 * vecDot u d + vecNormSq d := by
    calc
      vecNormSq (u + d) = vecDot (u + d) (u + d) := rfl
      _ = vecDot u (u + d) + vecDot d (u + d) := vecDot_add_left u d (u + d)
      _ = vecDot u u + vecDot u d + (vecDot d u + vecDot d d) := by
        rw [vecDot_add_right, vecDot_add_right]
      _ = vecNormSq u + 2 * vecDot u d + vecNormSq d := by
        rw [show vecDot d u = vecDot u d from vecDot_comm d u]
        simp only [vecNormSq]
        ring
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq u d
  have hYoung : |vecDot u d| ≤ τ * vecNormSq u / 2 + τ⁻¹ * vecNormSq d / 2 := by
    apply abs_le_add_halves_of_sq_le_mul
    · calc
        (vecDot u d) ^ 2 ≤ vecNormSq u * vecNormSq d := hcs
        _ = (τ * vecNormSq u) * (τ⁻¹ * vecNormSq d) := by
          field_simp [hτ.ne']
    · exact mul_nonneg hτ.le (vecNormSq_nonneg u)
    · exact mul_nonneg (inv_nonneg.mpr hτ.le) (vecNormSq_nonneg d)
  have hdot : vecDot u d ≤ τ * vecNormSq u / 2 + τ⁻¹ * vecNormSq d / 2 :=
    le_trans (le_abs_self _) hYoung
  rw [hexpand]
  nlinarith [vecNormSq_nonneg u, vecNormSq_nonneg d]

/-- The normalized response energy is continuous under a flux-only cell-load
perturbation. The coefficient-dependent skew term cancels from the increment,
so no coefficient cap is needed for this estimate. -/
theorem frame_energy_bottom_perturbation_le (ν σ κ τ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (hτ : 0 < τ)
    (X : BlockVec 2) (d : Vec 2) :
    Response.responseFrameEnergyDensity ν σ κ (X + (0,d)) ≤
      (1 + τ) * Response.responseFrameEnergyDensity ν σ κ X +
        (1 + τ⁻¹) * (σ / ν) * vecNormSq d := by
  rcases X with ⟨p,q⟩
  let u := q - (κ / σ) • matVecMul Response.responsePlanarJ p
  have hflux : (q + d) - (κ / σ) • matVecMul Response.responsePlanarJ p = u + d := by
    dsimp [u]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hnorm := vecNormSq_add_young u d hτ
  have hνσ : 0 ≤ ν / σ := div_nonneg hν.le hσ.le
  have hσν : 0 ≤ σ / ν := div_nonneg hσ.le hν.le
  have hflux' := mul_le_mul_of_nonneg_left hnorm hσν
  rw [Response.responseFrameEnergyDensity, Response.responseFrameEnergyDensity]
  simp only [Prod.fst_add, Prod.snd_add, add_zero]
  rw [hflux]
  rw [show q - (κ / σ) • matVecMul Response.responsePlanarJ p = u by rfl]
  have hpnon : 0 ≤ (ν / σ) * vecNormSq p := mul_nonneg hνσ (vecNormSq_nonneg p)
  nlinarith [hflux', hpnon]

end ASDExplicitGamma.Scalar
