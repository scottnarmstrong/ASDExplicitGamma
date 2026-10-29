module

public import ASDExplicitGamma.Scalar.PsdFormMaps
public import ASDExplicitGamma.Scalar.FlatSourceHaarLimit
public import ASDExplicitGamma.Scalar.FlatSourceQ3PositiveHaar
public import ASDExplicitGamma.Triadic.HaarNormTriangle
public import ASDExplicitGamma.Variational.LemmaVTiles

/-! The tiled positive-Haar energy `lemmaVTiledPositiveEnergy Q m` as the monotone
limit of positive-semidefinite forms on the module of admissible fields. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Triadic ASDExplicitGamma.Variational Filter Topology
open scoped BigOperators

/-- The energy of a scalar multiple. -/
theorem energy_const_mul' (Q : TriadicCube 2) (c : ℝ) (f : Vec 2 → ℝ) :
    energy Q (fun x => c * f x) = c ^ 2 * energy Q f := by
  rw [energy_eq_integral_sq Q, energy_eq_integral_sq Q]
  calc
    (∫ x, (c * f x) ^ 2 ∂normalizedCubeMeasure Q) =
        ∫ x, c ^ 2 * f x ^ 2 ∂normalizedCubeMeasure Q := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = c ^ 2 * ∫ x, f x ^ 2 ∂normalizedCubeMeasure Q := integral_const_mul _ _

/-- Fields with `L²` coordinates and summable positive-Haar increments on every tile
of depth `m`. -/
def TiledHaarAdmissible (Q : TriadicCube 2) (m : ℕ) (F : Vec 2 → Vec 2) : Prop :=
  ∀ R ∈ descendantsAtDepth Q m, ∀ i : Fin 2,
    MemLp (fun x => F x i) 2 (normalizedCubeMeasure R) ∧
      Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
        energy R (cubeIncrement R (k + 1) (fun x => F x i)))

/-- The module of tile-admissible fields. -/
def TiledHaarField (Q : TriadicCube 2) (m : ℕ) : Submodule ℝ (Vec 2 → Vec 2) where
  carrier := {F | TiledHaarAdmissible Q m F}
  zero_mem' := by
    intro R _ i
    refine ⟨?_, ?_⟩
    · simpa using (MemLp.zero : MemLp (fun _ : Vec 2 => (0 : ℝ)) 2 (normalizedCubeMeasure R))
    · have h0 : ∀ k : ℕ, energy R (cubeIncrement R (k + 1) (fun _ : Vec 2 => (0 : ℝ))) = 0 := by
        intro k
        have := cubeIncrement_smul R (k + 1) (fun _ : Vec 2 => (0 : ℝ)) 0
        simp only [zero_mul] at this
        rw [this]
        simp [energy_eq_integral_sq]
      refine (summable_zero (α := ℝ)).congr fun k => ?_
      change (0 : ℝ) = (Real.sqrt 3) ^ (k + 1) *
        energy R (cubeIncrement R (k + 1) (fun _ : Vec 2 => (0 : ℝ)))
      rw [h0 k, mul_zero]
  add_mem' := by
    intro F G hF hG R hR i
    obtain ⟨hFm, hFs⟩ := hF R hR i
    obtain ⟨hGm, hGs⟩ := hG R hR i
    exact ⟨hFm.add hGm, (positiveHaarNorm_add_le R hFm hGm hFs hGs).1⟩
  smul_mem' := by
    intro c F hF R hR i
    obtain ⟨hFm, hFs⟩ := hF R hR i
    refine ⟨hFm.const_mul c, ?_⟩
    have hs := hFs.mul_left (c ^ 2)
    refine hs.congr fun k => ?_
    change c ^ 2 * ((Real.sqrt 3) ^ (k + 1) * energy R (cubeIncrement R (k + 1) (fun x => F x i))) =
      (Real.sqrt 3) ^ (k + 1) *
        energy R (cubeIncrement R (k + 1) (fun x => c * F x i))
    rw [cubeIncrement_smul R (k + 1) (fun x => F x i) c, energy_const_mul']
    ring

section Forms

variable (Q : TriadicCube 2) (m : ℕ)

/-- The `L²` class of a coordinate on a tile. -/
noncomputable def tileCoordLp (R : descendantsAtDepth Q m) (i : Fin 2) :
    TiledHaarField Q m →ₗ[ℝ] Lp ℝ 2 (normalizedCubeMeasure R.1) where
  toFun F := ((F.2 R.1 R.2 i).1).toLp (fun x => F.1 x i)
  map_add' F G := by
    have h := MemLp.toLp_add ((F.2 R.1 R.2 i).1) ((G.2 R.1 R.2 i).1)
    exact h
  map_smul' c F := by
    have h := MemLp.toLp_const_smul (c := c) ((F.2 R.1 R.2 i).1)
    exact h

theorem tileCoordLp_ae (R : descendantsAtDepth Q m) (i : Fin 2) (F : TiledHaarField Q m) :
    (fun x => tileCoordLp Q m R i F x) =ᵐ[normalizedCubeMeasure R.1] fun x => F.1 x i :=
  ((F.2 R.1 R.2 i).1).coeFn_toLp

/-- Haar increment of the tile coordinate. -/
noncomputable def tileHaarMap (j : descendantsAtDepth Q m × Fin 2 × ℕ) :
    TiledHaarField Q m →ₗ[ℝ] Lp ℝ 2 (normalizedCubeMeasure j.1.1) :=
  (cubeIncrementL2CLM j.1.1 j.2.2).toLinearMap.comp (tileCoordLp Q m j.1 j.2.1)

theorem tileHaarMap_norm_sq (j : descendantsAtDepth Q m × Fin 2 × ℕ) (F : TiledHaarField Q m) :
    ‖tileHaarMap Q m j F‖ ^ 2 = energy j.1.1 (cubeIncrement j.1.1 j.2.2 (fun x => F.1 x j.2.1)) := by
  change ‖cubeIncrementL2CLM j.1.1 j.2.2 (tileCoordLp Q m j.1 j.2.1 F)‖ ^ 2 = _
  rw [← energy_cubeIncrement_eq_clm_norm_sq]
  rw [cubeIncrement_congr_ae j.1.1 j.2.2 (tileCoordLp_ae Q m j.1 j.2.1 F)]

/-- Weight of a Haar piece. -/
noncomputable def tileWeight (j : descendantsAtDepth Q m × Fin 2 × ℕ) : ℝ :=
  (Real.sqrt 3) ^ j.2.2 / ((descendantsAtDepth Q m).card : ℝ)

theorem tileWeight_nonneg (j : descendantsAtDepth Q m × Fin 2 × ℕ) : 0 ≤ tileWeight Q m j := by
  unfold tileWeight
  positivity

/-- The partial tiled positive-Haar form with Haar levels `0..N`. -/
noncomputable def tiledPartialForm (N : ℕ) : PsdForm (TiledHaarField Q m) :=
  PsdForm.ofMaps (H := fun j : descendantsAtDepth Q m × Fin 2 × ℕ =>
      Lp ℝ 2 (normalizedCubeMeasure j.1.1))
    (Finset.univ ×ˢ Finset.univ ×ˢ Finset.range (N + 1)) (tileHaarMap Q m) (tileWeight Q m)
    (tileWeight_nonneg Q m)

theorem tiledPartialForm_self (N : ℕ) (a : TiledHaarField Q m) :
    (tiledPartialForm Q m N).form a a =
      descendantsAverage Q m (fun R => ∑ i : Fin 2,
        partialEnergy R (Real.sqrt 3) N (fun x => a.1 x i)) := by
  classical
  unfold tiledPartialForm
  rw [PsdForm.ofMaps_apply_self]
  simp only [tileHaarMap_norm_sq, tileWeight]
  rw [Finset.sum_product]
  simp only [Finset.sum_product]
  unfold descendantsAverage
  dsimp only
  rw [← Finset.sum_coe_sort (descendantsAtDepth Q m)
    (fun R => ∑ i : Fin 2, partialEnergy R (Real.sqrt 3) N (fun x => (a.1 x i)))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold partialEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end Forms

section Limit

variable (Q : TriadicCube 2) (m : ℕ)

theorem tiled_summable_all (R : TriadicCube 2) {f : Vec 2 → ℝ}
    (hs : Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
        energy R (cubeIncrement R (k + 1) f))) :
    Summable (fun k : ℕ => (Real.sqrt 3) ^ k * energy R (cubeIncrement R k f)) :=
  (summable_nat_add_iff 1).1 hs

theorem partialEnergy_tendsto_primal (R : TriadicCube 2) {f : Vec 2 → ℝ}
    (hs : Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
        energy R (cubeIncrement R (k + 1) f))) :
    Tendsto (fun N => partialEnergy R (Real.sqrt 3) N f) atTop (𝓝 (primalEnergy R (Real.sqrt 3) f)) := by
  have hall := tiled_summable_all R hs
  rw [primalEnergy_eq_tsum R _ f hall]
  exact (hall.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)

theorem partialEnergy_le_primal (R : TriadicCube 2) {f : Vec 2 → ℝ}
    (hs : Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
        energy R (cubeIncrement R (k + 1) f))) (N : ℕ) :
    partialEnergy R (Real.sqrt 3) N f ≤ primalEnergy R (Real.sqrt 3) f := by
  have hall := tiled_summable_all R hs
  rw [primalEnergy_eq_tsum R _ f hall]
  exact hall.sum_le_tsum _ (fun k _ => mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (energy_nonneg R _))

/-- The tiled positive-Haar energy of an admissible field. -/
noncomputable def tiledPositiveEnergy (a : TiledHaarField Q m) : ℝ :=
  lemmaVTiledPositiveEnergy Q m a.1

theorem tiledPartialForm_le (N : ℕ) (a : TiledHaarField Q m) :
    (tiledPartialForm Q m N).form a a ≤ tiledPositiveEnergy Q m a := by
  rw [tiledPartialForm_self]
  unfold tiledPositiveEnergy lemmaVTiledPositiveEnergy
  refine descendantsAverage_le_descendantsAverage Q m fun R hR => ?_
  unfold vectorPositiveHaarEnergy
  exact Finset.sum_le_sum fun i _ => partialEnergy_le_primal R ((a.2 R hR i).2) N

theorem tiledPartialForm_tendsto (a : TiledHaarField Q m) :
    Tendsto (fun N => (tiledPartialForm Q m N).form a a) atTop (𝓝 (tiledPositiveEnergy Q m a)) := by
  classical
  simp only [tiledPartialForm_self]
  unfold tiledPositiveEnergy lemmaVTiledPositiveEnergy descendantsAverage
  dsimp only
  refine Tendsto.const_mul _ ?_
  refine tendsto_finset_sum _ fun R hR => ?_
  unfold vectorPositiveHaarEnergy
  exact tendsto_finset_sum _ fun i _ => partialEnergy_tendsto_primal R ((a.2 R hR i).2)

end Limit

end ASDExplicitGamma.Scalar
