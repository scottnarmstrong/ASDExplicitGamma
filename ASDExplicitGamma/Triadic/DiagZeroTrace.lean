module

public import ASDExplicitGamma.Triadic.DiagSobolev
import Mathlib.Tactic.Push

/-! Boundary-touching tensor hats belong to the actual H¹₀ approximation carrier. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Filter Set
open scoped Topology

noncomputable section

theorem diagHatSlope_tendsto_radius {r : ℝ} (hr : r ≠ 0) {ρ : ℕ → ℝ}
    (hρ : Tendsto ρ atTop (𝓝 r)) (t : ℝ) (hl : t ≠ -r) (hu : t ≠ r) :
    Tendsto (fun n => diagHatSlope (ρ n) t) atTop (𝓝 (diagHatSlope r t)) := by
  have hleft : ∀ᶠ n in atTop, (-ρ n < t) ↔ (-r < t) := by
    rcases lt_or_gt_of_ne hl with ht | ht
    · have hn := (tendsto_order.1 hρ).2 (-t) (by linarith only [ht])
      filter_upwards [hn] with n hn
      constructor <;> intro h <;> linarith only [hn, ht, h]
    · have hn := (tendsto_order.1 hρ).1 (-t) (by linarith only [ht])
      filter_upwards [hn] with n hn
      constructor <;> intro h <;> linarith only [hn, ht, h]
  have hright : ∀ᶠ n in atTop, (ρ n < t) ↔ (r < t) := by
    rcases lt_or_gt_of_ne hu with ht | ht
    · have hn := (tendsto_order.1 hρ).1 t ht
      filter_upwards [hn] with n hn
      constructor <;> intro h <;> linarith only [hn, ht, h]
    · have hn := (tendsto_order.1 hρ).2 t ht
      filter_upwards [hn] with n hn
      constructor <;> intro h <;> linarith only [hn, ht, h]
  have hlim : Tendsto (fun n =>
      ((if -r < t then (1 : ℝ) else 0) - 2 * (if 0 < t then 1 else 0) +
        (if r < t then 1 else 0)) / ρ n) atTop (𝓝 (diagHatSlope r t)) :=
    tendsto_const_nhds.div hρ hr
  apply hlim.congr'
  filter_upwards [hleft, hright] with n hn hn'
  simp only [diagHatSlope, hn, hn']

theorem diagPhysicalHat_zero_off_box (c : Vec 2) {r : ℝ} (hr : 0 < r)
    (x : Vec 2) (hx : x ∉ Set.pi univ (fun i => Icc (c i - r) (c i + r))) :
    diagPhysicalHat c r x = 0 := by
  have hex : ∃ i, x i < c i - r ∨ c i + r < x i := by
    simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc, not_forall,
      not_and_or, not_le] at hx
    exact hx
  obtain ⟨i, hi⟩ := hex
  unfold diagPhysicalHat tensorMultiplier
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply diagHat_eq_zero
  rw [abs_div, abs_of_pos hr]
  apply (le_div_iff₀ hr).2
  rw [one_mul]
  rcases hi with hi | hi
  · exact (by linarith only [hi] : r ≤ -(x i - c i)).trans (neg_le_abs _)
  · exact (by linarith only [hi] : r ≤ x i - c i).trans (le_abs_self _)

/-- An interior hat may touch the parent faces, but its smooth-closure trace
still vanishes. Shrunk hats are compactly supported strictly inside the cube. -/
theorem diagPhysicalHat_memH10 (Q : TriadicCube 2) (c : Vec 2) {r : ℝ} (hr : 0 < r)
    (hc : ∀ i, cubeCorner Q i ≤ c i - r ∧
      c i + r ≤ cubeCorner Q i + cubeScaleFactor Q) :
    MemH10 (openCubeSet Q) (diagPhysicalHat c r) := by
  let ρ : ℕ → ℝ := fun n => r * (1 - 1 / ((n : ℝ) + 2))
  have hρlo (n : ℕ) : r / 2 ≤ ρ n := by
    have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hi : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn
    dsimp [ρ]
    nlinarith only [hi, hr]
  have hρpos (n : ℕ) : 0 < ρ n := (half_pos hr).trans_le (hρlo n)
  have hρlt (n : ℕ) : ρ n < r := by
    have hi : 0 < 1 / ((n : ℝ) + 2) := by positivity
    dsimp [ρ]
    nlinarith only [hi, hr]
  have hρlim : Tendsto ρ atTop (𝓝 r) := by
    have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa only [sub_zero, mul_one] using (hε.const_sub (1 : ℝ)).const_mul r
  let f := diagPhysicalHatH1 Q c r hr
  let F (n : ℕ) := diagPhysicalHatH1 Q c (ρ n) (hρpos n)
  have hmem (n : ℕ) : MemH10 (openCubeSet Q) (F n).toFun := by
    let K := Set.pi univ (fun i : Fin 2 => Icc (c i - ρ n) (c i + ρ n))
    apply memH10_of_compactSupport (isOpenBoundedConvexDomain_openCubeSet Q) (F n)
      (K := K) (isCompact_univ_pi fun _ => isCompact_Icc)
    · intro x hx
      rw [openCubeSet_eq_box]
      intro i _
      have hi := hx i (Set.mem_univ i)
      have hc' := hc i
      exact ⟨by linarith only [hi.1, hc'.1, hρlt n],
        by linarith only [hi.2, hc'.2, hρlt n]⟩
    · intro x hx
      exact diagPhysicalHat_zero_off_box c (hρpos n) x hx
  have hf (x : Vec 2) : Tendsto (fun n => (F n).toFun x) atTop (𝓝 (f.toFun x)) := by
    simp only [F, f, diagPhysicalHatH1_toFun, diagPhysicalHat, tensorMultiplier]
    apply tendsto_finsetProd
    intro i _
    exact diagHat_continuous.continuousAt.tendsto.comp
      (tendsto_const_nhds.div hρlim hr.ne')
  have hdf (i : Fin 2) : ∀ᵐ x ∂(volume.restrict (openCubeSet Q)),
      Tendsto (fun n => (F n).grad x i) atTop (𝓝 (f.grad x i)) := by
    have hl : ∀ᵐ x : Vec 2 ∂volume, x i ≠ c i - r := Measure.ae_eval_ne (fun _ : Fin 2 => volume) i _
    have hu : ∀ᵐ x : Vec 2 ∂volume, x i ≠ c i + r := Measure.ae_eval_ne (fun _ : Fin 2 => volume) i _
    filter_upwards [ae_restrict_of_ae hl, ae_restrict_of_ae hu] with x hl hu
    simp only [F, f, diagPhysicalHatH1_grad, diagPhysicalHatGradient, tensorDerivative]
    apply (diagHatSlope_tendsto_radius hr.ne' hρlim (x i - c i)
      (by intro h; apply hl; linarith only [h])
      (by intro h; apply hu; linarith only [h])).mul
    apply tendsto_finsetProd
    intro k _
    exact diagHat_continuous.continuousAt.tendsto.comp
      (tendsto_const_nhds.div hρlim hr.ne')
  have hb (n : ℕ) (x : Vec 2) : ‖(F n).toFun x‖ ≤ 1 := by
    have h := norm_tensorMultiplier_le (fun i t => diagHat ((t - c i) / ρ n)) x
      (M := 1) (fun i => by
        rw [Real.norm_eq_abs, abs_of_nonneg (diagHat_nonneg _)]
        exact diagHat_le_one _)
    simpa only [F, diagPhysicalHatH1_toFun, diagPhysicalHat, one_pow] using h
  let M : ℝ := 1 + 8 / r
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have h1M : (1 : ℝ) ≤ M := by
    dsimp [M]
    linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 8) hr.le]
  have hdb (n : ℕ) (x : Vec 2) (i : Fin 2) : ‖(F n).grad x i‖ ≤ M ^ 2 := by
    simp only [F, diagPhysicalHatH1_grad, diagPhysicalHatGradient]
    apply norm_tensorDerivative_le _ _ x i hM
    · intro k
      rw [Real.norm_eq_abs, abs_of_nonneg (diagHat_nonneg _)]
      exact (diagHat_le_one _).trans h1M
    · have hdiv : 4 / ρ n ≤ 8 / r := by
        apply (div_le_div_iff₀ (hρpos n) hr).2
        nlinarith only [hρlo n]
      exact (diagHatSlope_bound (hρpos n) _).trans (hdiv.trans (by dsimp [M]; linarith))
  have : IsFiniteMeasure (volume.restrict (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isBoundedDomain.isFiniteMeasure_restrict_volume
  apply memH10_of_tendsto_H1 (isOpenBoundedConvexDomain_openCubeSet Q) f F hmem
  · rw [show (fun n => eLpNorm (fun x => f.toFun x - (F n).toFun x) 2
        (volumeMeasureOn (openCubeSet Q))) =
      (fun n => eLpNorm (fun x => (F n).toFun x - f.toFun x) 2
        (volumeMeasureOn (openCubeSet Q))) from funext fun n => eLpNorm_sub_swap _ _]
    exact tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
      (fun n => (F n).memL2.aestronglyMeasurable) f.memL2 (memLp_const 1)
      (fun n => Filter.Eventually.of_forall (hb n)) (Filter.Eventually.of_forall hf)
  · intro i
    rw [show (fun n => eLpNorm (fun x => f.grad x i - (F n).grad x i) 2
        (volumeMeasureOn (openCubeSet Q))) =
      (fun n => eLpNorm (fun x => (F n).grad x i - f.grad x i) 2
        (volumeMeasureOn (openCubeSet Q))) from funext fun n => eLpNorm_sub_swap _ _]
    exact tendsto_eLpNorm_two_of_tendsto_ae_of_dominated
      (fun n => ((F n).gradMemL2 i).aestronglyMeasurable) (f.gradMemL2 i)
      (memLp_const (M ^ 2)) (fun n => Filter.Eventually.of_forall fun x => hdb n x i) (hdf i)

end

end ASDExplicitGamma.Triadic
