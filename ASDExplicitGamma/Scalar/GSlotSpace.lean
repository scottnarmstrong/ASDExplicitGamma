module

public import ASDExplicitGamma.Scalar.PsdTiledHaar
public import ASDExplicitGamma.Scalar.GSlotHaar
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The Hilbert space `ℓ²` of weighted tile Haar increments, in which the positive norm
`tiledPositiveEnergy` and the weak norm `lemmaVTiledWeakEnergy` are both Hilbert norms. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators Topology InnerProductSpace ENNReal

noncomputable section

variable (Q : TriadicCube 2) (m : ℕ)

/-- Index set of the Haar pieces: tile, coordinate, Haar level. -/
abbrev GIdx := descendantsAtDepth Q m × Fin 2 × ℕ

/-- The fibre at a Haar piece. -/
abbrev GFib (j : GIdx Q m) : Type := ↥(Lp ℝ 2 (normalizedCubeMeasure j.1.1))

/-- The Hilbert space of weighted Haar increment sequences. -/
abbrev GSpace := ↥(lp (GFib Q m) 2)

variable {Q m}

theorem summable_GIdx {f : GIdx Q m → ℝ} (h0 : ∀ j, 0 ≤ f j)
    (h : ∀ (R : descendantsAtDepth Q m) (i : Fin 2), Summable (fun k : ℕ => f (R, i, k))) :
    Summable f := by
  rw [summable_prod_of_nonneg h0]
  refine ⟨fun R => ?_, Summable.of_finite⟩
  have h0' : ∀ b : Fin 2 × ℕ, 0 ≤ f (R, b) := fun b => h0 _
  rw [summable_prod_of_nonneg h0']
  exact ⟨fun i => h R i, Summable.of_finite⟩

theorem tsum_GIdx {f : GIdx Q m → ℝ} (hs : Summable f) :
    ∑' j, f j = ∑ R : descendantsAtDepth Q m, ∑ i : Fin 2, ∑' k : ℕ, f (R, i, k) := by
  rw [hs.tsum_prod' (fun R => hs.prod_factor R), tsum_fintype]
  refine Finset.sum_congr rfl fun R _ => ?_
  have hR : Summable (fun b : Fin 2 × ℕ => f (R, b)) := hs.prod_factor R
  rw [hR.tsum_prod' (fun i => hR.prod_factor i), tsum_fintype]

theorem card_pos' (Q : TriadicCube 2) (m : ℕ) : (0 : ℝ) < (descendantsAtDepth Q m).card := by
  exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q m)

/-- Tile coordinates. -/
abbrev GCoord (Q : TriadicCube 2) (m : ℕ) : Type :=
  ∀ (R : descendantsAtDepth Q m) (_ : Fin 2), ↥(Lp ℝ 2 (normalizedCubeMeasure R.1))

/-- Weight `q^k / card` of a Haar piece. -/
def gWt (q : ℝ) (j : GIdx Q m) : ℝ := q ^ j.2.2 / ((descendantsAtDepth Q m).card : ℝ)

theorem gWt_nonneg {q : ℝ} (hq : 0 ≤ q) (j : GIdx Q m) : 0 ≤ gWt q j := by
  have := card_pos' Q m
  unfold gWt; positivity

/-- The weighted increment sequence of tile coordinates. -/
def gseqFun (q : ℝ) (f : GCoord Q m) : ∀ j : GIdx Q m, GFib Q m j :=
  fun j => Real.sqrt (gWt q j) • cubeIncrementL2CLM j.1.1 j.2.2 (f j.1 j.2.1)

theorem gseqFun_norm_sq {q : ℝ} (hq : 0 ≤ q) (f : GCoord Q m) (j : GIdx Q m) :
    ‖gseqFun q f j‖ ^ 2 =
      gWt q j * energy j.1.1 (cubeIncrement j.1.1 j.2.2 (fun x => f j.1 j.2.1 x)) := by
  unfold gseqFun
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (gWt_nonneg hq j),
    ← energy_cubeIncrement_eq_clm_norm_sq]

theorem gseq_summable {q : ℝ} (hq : 0 ≤ q) (f : GCoord Q m)
    (h : ∀ (R : descendantsAtDepth Q m) (i : Fin 2),
      Summable (fun k : ℕ => q ^ k * energy R.1 (cubeIncrement R.1 k (fun x => f R i x)))) :
    Summable (fun j : GIdx Q m => ‖gseqFun q f j‖ ^ 2) := by
  refine summable_GIdx (fun j => by positivity) (fun R i => ?_)
  have := (h R i).mul_left (((descendantsAtDepth Q m).card : ℝ)⁻¹)
  refine this.congr fun k => ?_
  rw [gseqFun_norm_sq hq]
  simp only [gWt]
  ring

/-- The `ℓ²` element of a weighted increment sequence. -/
def gseq {q : ℝ} (hq : 0 ≤ q) (f : GCoord Q m)
    (h : ∀ (R : descendantsAtDepth Q m) (i : Fin 2),
      Summable (fun k : ℕ => q ^ k * energy R.1 (cubeIncrement R.1 k (fun x => f R i x)))) :
    GSpace Q m :=
  ⟨gseqFun q f, memℓp_gen (by simpa using gseq_summable hq f h)⟩

/-- Norm identity: `‖gseq‖² = card⁻¹ ∑ primalEnergy`. -/
theorem gseq_norm_sq {q : ℝ} (hq : 0 ≤ q) (f : GCoord Q m) (h) :
    ‖(gseq hq f h : GSpace Q m)‖ ^ 2 =
      ((descendantsAtDepth Q m).card : ℝ)⁻¹ * ∑ R : descendantsAtDepth Q m, ∑ i : Fin 2,
        primalEnergy R.1 q (fun x => f R i x) := by
  have hn := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (gseq hq f h)
  have hs := gseq_summable hq f h
  rw [show ((2 : ℝ≥0∞).toReal) = 2 by norm_num] at hn
  rw [show (‖(gseq hq f h : GSpace Q m)‖ ^ (2 : ℝ)) = ‖(gseq hq f h : GSpace Q m)‖ ^ 2 from
    Real.rpow_two _] at hn
  rw [hn]
  have hfun : ∀ j, ‖(gseq hq f h : GSpace Q m) j‖ ^ (2 : ℝ) = ‖gseqFun q f j‖ ^ 2 := fun j => by
    rw [Real.rpow_two]; rfl
  simp only [hfun]
  rw [tsum_GIdx hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hall := h R i
  rw [primalEnergy_eq_tsum R.1 q _ hall, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [gseqFun_norm_sq hq]
  simp only [gWt]
  ring

theorem gseq_inner {q1 q2 : ℝ} (h1 : 0 ≤ q1) (h2 : 0 ≤ q2) (hq : q1 * q2 = 1)
    (f g : GCoord Q m) (hf) (hg) :
    ⟪(gseq h1 f hf : GSpace Q m), (gseq h2 g hg : GSpace Q m)⟫_ℝ =
      ((descendantsAtDepth Q m).card : ℝ)⁻¹ * ∑ R : descendantsAtDepth Q m, ∑ i : Fin 2,
        ⟪f R i, g R i⟫_ℝ := by
  rw [lp.inner_eq_tsum (𝕜 := ℝ)]
  have hs := lp.summable_inner (𝕜 := ℝ) (gseq h1 f hf) (gseq h2 g hg)
  rw [tsum_GIdx hs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc := card_pos' Q m
  have hk : ∀ k : ℕ, ⟪(gseq h1 f hf : GSpace Q m) (R, i, k), (gseq h2 g hg : GSpace Q m) (R, i, k)⟫_ℝ =
      ((descendantsAtDepth Q m).card : ℝ)⁻¹ *
        ⟪cubeIncrementL2CLM R.1 k (f R i), cubeIncrementL2CLM R.1 k (g R i)⟫_ℝ := by
    intro k
    change ⟪gseqFun q1 f (R, i, k), gseqFun q2 g (R, i, k)⟫_ℝ = _
    unfold gseqFun
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
      ← Real.sqrt_mul (gWt_nonneg h1 _)]
    have : gWt q1 (R, i, k) * gWt q2 (R, i, k) =
        (((descendantsAtDepth Q m).card : ℝ)⁻¹) ^ 2 := by
      simp only [gWt]
      rw [show q1 ^ k / ((descendantsAtDepth Q m).card : ℝ) * (q2 ^ k / ((descendantsAtDepth Q m).card : ℝ)) =
        (q1 * q2) ^ k * (((descendantsAtDepth Q m).card : ℝ)⁻¹) ^ 2 by
          rw [mul_pow]; field_simp, hq, one_pow, one_mul]
    rw [this, Real.sqrt_sq (by positivity)]
  simp only [hk]
  exact ((inner_hasSum R.1 (f R i) (g R i)).mul_left _).tsum_eq

/-- Discounted increment energies of any `L²` coordinate are summable for `0 ≤ q ≤ 1`. -/
theorem gseq_summable_weak {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (R : TriadicCube 2)
    (u : Lp ℝ 2 (normalizedCubeMeasure R)) :
    Summable (fun k : ℕ => q ^ k * energy R (cubeIncrement R k (fun x => u x))) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg hq _) (energy_nonneg R _))
    (fun k => ?_) (summable_cubeIncrement_energy R (Lp.memLp u))
  have := pow_le_one₀ hq hq1 (n := k)
  nlinarith [energy_nonneg R (cubeIncrement R k (fun x => u x))]

end

end ASDExplicitGamma.Scalar
