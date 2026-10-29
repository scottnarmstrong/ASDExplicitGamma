module

public import ASDExplicitGamma.Scalar.GSlotMaps
public import ASDExplicitGamma.Scalar.GSlotSynthParts

/-! Synthesis of a tile field from an increment sequence: the range of `Φ` consists of
the sequences `c` with `c_j = inc_j c_j`, and for every `c : ℓ²` there is a tile field `G` with
`Φ G = (inc_j c_j)_j`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators Topology InnerProductSpace ENNReal

noncomputable section

variable {Q : TriadicCube 2} {m : ℕ}

theorem c_sq_summable (c : GSpace Q m) : Summable (fun j : GIdx Q m => ‖c j‖ ^ 2) := by
  have h := (memℓp_gen_iff (p := 2) (by norm_num)).1 c.2
  simpa using h

/-- Inverse square root of the Haar weight. -/
def gAinv (j : GIdx Q m) : ℝ := (Real.sqrt (gWt (Real.sqrt 3) j))⁻¹

theorem gWt_pos (j : GIdx Q m) : 0 < gWt (Real.sqrt 3) j := by
  have := card_pos' Q m
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  unfold gWt; positivity

theorem gAinv_mul (j : GIdx Q m) : Real.sqrt (gWt (Real.sqrt 3) j) * gAinv j = 1 := by
  unfold gAinv
  exact mul_inv_cancel₀ (Real.sqrt_pos.2 (gWt_pos j)).ne'

theorem gAinv_sq_mul (j : GIdx Q m) :
    (gAinv j) ^ 2 * (Real.sqrt 3) ^ j.2.2 = ((descendantsAtDepth Q m).card : ℝ) := by
  have hc := card_pos' Q m
  have h3 : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  unfold gAinv
  rw [inv_pow, Real.sq_sqrt (gWt_pos j).le]
  unfold gWt
  field_simp

theorem gAinv_sq_le (j : GIdx Q m) : (gAinv j) ^ 2 ≤ ((descendantsAtDepth Q m).card : ℝ) := by
  have h1 : (1 : ℝ) ≤ (Real.sqrt 3) ^ j.2.2 := one_le_pow₀ (by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num))
  have := gAinv_sq_mul j
  have h0 : 0 ≤ (gAinv j) ^ 2 := sq_nonneg _
  nlinarith

/-- The tile limit of the synthesised increments. -/
def gTile (c : GSpace Q m) (R : descendantsAtDepth Q m) (i : Fin 2) :
    Lp ℝ 2 (normalizedCubeMeasure R.1) :=
  ∑' k : ℕ, incL R.1 k (gAinv (R, i, k) • c (R, i, k))

theorem gTile_summable (c : GSpace Q m) (R : descendantsAtDepth Q m) (i : Fin 2) :
    Summable (fun k : ℕ => incL R.1 k (gAinv (R, i, k) • c (R, i, k))) := by
  refine summable_inc R.1 _ ?_
  have hs : Summable (fun k : ℕ => ‖c (R, i, k)‖ ^ 2) :=
    (c_sq_summable c).comp_injective (fun a b h => by simpa using h)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (hs.mul_left ((descendantsAtDepth Q m).card : ℝ))
  have h1 : ‖incL R.1 k (gAinv (R, i, k) • c (R, i, k))‖ ^ 2 ≤
      (gAinv (R, i, k)) ^ 2 * ‖c (R, i, k)‖ ^ 2 := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_inc_le R.1 k _) 2) (sq_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_right (gAinv_sq_le _) (sq_nonneg _))

theorem gTile_inc (c : GSpace Q m) (R : descendantsAtDepth Q m) (i : Fin 2) (k : ℕ) :
    incL R.1 k (gTile c R i) = gAinv (R, i, k) • incL R.1 k (c (R, i, k)) := by
  unfold gTile
  rw [inc_tsum R.1 (fun k => gAinv (R, i, k) • c (R, i, k)) (gTile_summable c R i) k,
    map_smul]

/-- The synthesised tile field. -/
def gField (c : GSpace Q m) : Vec 2 → Vec 2 := fun x i =>
  ∑ R : descendantsAtDepth Q m,
    (cubeSet R.1).indicator (fun y => (gTile c R i : Lp ℝ 2 (normalizedCubeMeasure R.1)) y) x

theorem gField_apply (c : GSpace Q m) (R : descendantsAtDepth Q m) {x : Vec 2}
    (hx : x ∈ cubeSet R.1) (i : Fin 2) : gField c x i = gTile c R i x := by
  unfold gField
  rw [Finset.sum_eq_single R]
  · simp [Set.indicator_of_mem hx]
  · intro R' _ hne
    refine Set.indicator_of_notMem (fun hx' => ?_) _
    have hd := pairwiseDisjoint_descendantsAtDepth Q m (Finset.mem_coe.2 R'.2)
      (Finset.mem_coe.2 R.2) (fun h => hne (Subtype.ext h))
    exact Set.disjoint_left.1 hd hx' hx
  · intro h; exact absurd (Finset.mem_univ R) h

theorem gField_ae (c : GSpace Q m) (R : descendantsAtDepth Q m) (i : Fin 2) :
    (fun x => gField c x i) =ᵐ[normalizedCubeMeasure R.1] fun x => gTile c R i x := by
  have h : ∀ᵐ x ∂(volume.restrict (cubeSet R.1)), gField c x i = gTile c R i x :=
    ae_restrict_of_forall_mem (measurableSet_cubeSet R.1) (fun x hx => gField_apply c R hx i)
  exact Measure.ae_smul_measure h _

theorem gField_admissible (c : GSpace Q m) : TiledHaarAdmissible Q m (gField c) := by
  intro R hR i
  let R' : descendantsAtDepth Q m := ⟨R, hR⟩
  refine ⟨(Lp.memLp (gTile c R' i)).ae_eq (gField_ae c R' i).symm, ?_⟩
  have hs : Summable (fun k : ℕ => ‖c (R', i, k + 1)‖ ^ 2) :=
    (c_sq_summable c).comp_injective (fun a b h => by simpa using h)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
    (energy_nonneg _ _)) (fun k => ?_) (hs.mul_left ((descendantsAtDepth Q m).card : ℝ))
  have hg : incL R (k + 1) (gTile c R' i) =
      gAinv (R', i, k + 1) • incL R (k + 1) (c (R', i, k + 1)) := gTile_inc c R' i (k + 1)
  have h1 : energy R (cubeIncrement R (k + 1) (fun x => gField c x i)) =
      (gAinv (R', i, k + 1)) ^ 2 * ‖incL R (k + 1) (c (R', i, k + 1))‖ ^ 2 := by
    rw [cubeIncrement_congr_ae R (k + 1) (gField_ae c R' i),
      energy_cubeIncrement_eq_clm_norm_sq]
    change ‖incL R (k + 1) (gTile c R' i)‖ ^ 2 = _
    rw [hg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [h1]
  have h2 := gAinv_sq_mul (R', i, k + 1)
  calc (Real.sqrt 3) ^ (k + 1) * ((gAinv (R', i, k + 1)) ^ 2 *
        ‖incL R (k + 1) (c (R', i, k + 1))‖ ^ 2)
      = ((gAinv (R', i, k + 1)) ^ 2 * (Real.sqrt 3) ^ (k + 1)) *
        ‖incL R (k + 1) (c (R', i, k + 1))‖ ^ 2 := by ring
    _ = ((descendantsAtDepth Q m).card : ℝ) * ‖incL R (k + 1) (c (R', i, k + 1))‖ ^ 2 := by
        rw [show (R', i, k + 1).2.2 = k + 1 from rfl] at h2
        rw [h2]
    _ ≤ ((descendantsAtDepth Q m).card : ℝ) * ‖c (R', i, k + 1)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
          (norm_inc_le R (k + 1) _) 2) (card_pos' Q m).le

theorem gField_memVectorL2 (c : GSpace Q m) : MemVectorL2 (openCubeSet Q) (gField c) := by
  refine MemLp.of_eval (fun i => ?_)
  change MemLp (fun x => ∑ R : descendantsAtDepth Q m, (cubeSet R.1).indicator
    (fun y => (gTile c R i : Lp ℝ 2 (normalizedCubeMeasure R.1)) y) x) 2
    (volumeMeasureOn (openCubeSet Q))
  refine memLp_finset_sum _ (fun R _ => ?_)
  have h1 : MemLp (fun y => (gTile c R i : Lp ℝ 2 (normalizedCubeMeasure R.1)) y) 2
      (volume.restrict (cubeSet R.1)) := by
    have := Lp.memLp (gTile c R i)
    unfold normalizedCubeMeasure cubeMeasure at this
    have h3 := this.smul_measure (c := ENNReal.ofReal (cubeVolume R.1)) ENNReal.ofReal_ne_top
    rwa [smul_smul, ← ENNReal.ofReal_mul (cubeVolume_pos R.1).le,
      mul_inv_cancel₀ (cubeVolume_pos R.1).ne', ENNReal.ofReal_one, one_smul] at h3
  have h2 : MemLp ((cubeSet R.1).indicator
      (fun y => (gTile c R i : Lp ℝ 2 (normalizedCubeMeasure R.1)) y)) 2 volume :=
    (memLp_indicator_iff_restrict (measurableSet_cubeSet R.1)).2 h1
  exact h2.restrict _

/-- **Synthesis.** For every `c : ℓ²` there is a tile field `G` with `Φ G = (inc_j c_j)_j`. -/
theorem gSynth (c : GSpace Q m) :
    ∃ G : TiledHaarField Q m, MemVectorL2 (openCubeSet Q) G.1 ∧ ∀ j : GIdx Q m,
      (PhiL Q m G : GSpace Q m) j = incL j.1.1 j.2.2 (c j) := by
  refine ⟨⟨gField c, gField_admissible c⟩, gField_memVectorL2 c, fun j => ?_⟩
  obtain ⟨R, i, k⟩ := j
  have hcoord : tileCoordLp Q m R i ⟨gField c, gField_admissible c⟩ = gTile c R i := by
    apply Lp.ext
    filter_upwards [tileCoordLp_ae Q m R i ⟨gField c, gField_admissible c⟩, gField_ae c R i]
      with x h1 h2
    rw [h1, h2]
  rw [phiL_apply]
  unfold gseqFun
  dsimp only
  rw [hcoord]
  have hg : incL R.1 k (gTile c R i) = gAinv (R, i, k) • incL R.1 k (c (R, i, k)) :=
    gTile_inc c R i k
  change Real.sqrt (gWt (Real.sqrt 3) (R, i, k)) • incL R.1 k (gTile c R i) = _
  rw [hg, smul_smul, gAinv_mul, one_smul]

end

end ASDExplicitGamma.Scalar
