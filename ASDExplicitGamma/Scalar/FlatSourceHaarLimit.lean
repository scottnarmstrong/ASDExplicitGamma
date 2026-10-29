module

public import ASDExplicitGamma.Triadic.PlanarConstants
public import ASDExplicitGamma.Triadic.PlanarPositiveGradient
public import ASDExplicitGamma.Triadic.TriadicDualNorms
import ASDExplicitGamma.Variational.LemmaVHaar

/-! Passage from uniform finite-depth Haar bounds to the full positive Haar norm. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter
open ASDExplicitGamma.Triadic
open scoped BigOperators Topology

theorem cubeIncrement_add_of_memLp'
    (Q : TriadicCube 2) (k : ℕ) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeIncrement Q k (fun x => f x + g x) =
      fun x => cubeIncrement Q k f x + cubeIncrement Q k g x := by
  cases k with
  | zero => exact projection_add Q 0 hf hg
  | succ k =>
      simp only [cubeIncrement_succ, projection_add Q _ hf hg]
      funext x
      ring

theorem cubeIncrement_smul
    (Q : TriadicCube 2) (k : ℕ) (f : Vec 2 → ℝ) (c : ℝ) :
    cubeIncrement Q k (fun x => c * f x) =
      fun x => c * cubeIncrement Q k f x := by
  cases k with
  | zero => simp [cubeIncrement_zero, projection_smul]
  | succ k =>
      simp only [cubeIncrement_succ, projection_smul]
      funext x
      ring

theorem cubeIncrement_congr_ae
    (Q : TriadicCube 2) (k : ℕ) {f g : Vec 2 → ℝ}
    (hfg : f =ᵐ[normalizedCubeMeasure Q] g) :
    cubeIncrement Q k f = cubeIncrement Q k g := by
  have hc : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.mpr (cubeVolume_pos Q)
  have hfg' : f =ᵐ[volume.restrict (cubeSet Q)] g := by
    have hfg'' : f =ᵐ[ENNReal.ofReal ((cubeVolume Q)⁻¹) •
        volume.restrict (cubeSet Q)] g := by
      simpa [normalizedCubeMeasure, cubeMeasure] using hfg
    exact (Measure.ae_ennreal_smul_measure_iff hc).mp hfg''
  have hp (j : ℕ) : cubeProjection Q j f = cubeProjection Q j g :=
    ASDExplicitGamma.Variational.lemmaV_cubeProjection_congr_ae Q j hfg'
  cases k with
  | zero => simpa only [cubeIncrement_zero] using hp 0
  | succ k =>
      rw [cubeIncrement_succ, cubeIncrement_succ, hp (k + 1), hp k]

theorem cubeIncrement_lp_add
    (Q : TriadicCube 2) (k : ℕ)
    (f g : Lp ℝ 2 (normalizedCubeMeasure Q)) :
    cubeIncrement Q k (fun x => (f + g) x) =
      fun x => cubeIncrement Q k f x + cubeIncrement Q k g x := by
  calc
    cubeIncrement Q k (fun x => (f + g) x) =
        cubeIncrement Q k (fun x => f x + g x) := by
          exact cubeIncrement_congr_ae Q k (Lp.coeFn_add f g)
    _ = fun x => cubeIncrement Q k f x + cubeIncrement Q k g x :=
      cubeIncrement_add_of_memLp' Q k (Lp.memLp f) (Lp.memLp g)

theorem cubeIncrement_lp_smul
    (Q : TriadicCube 2) (k : ℕ) (c : ℝ)
    (f : Lp ℝ 2 (normalizedCubeMeasure Q)) :
    cubeIncrement Q k (fun x => (c • f) x) =
      fun x => c * cubeIncrement Q k f x := by
  calc
    cubeIncrement Q k (fun x => (c • f) x) =
        cubeIncrement Q k (fun x => c * f x) := by
          apply cubeIncrement_congr_ae Q k
          filter_upwards [Lp.coeFn_smul c f] with x hx
          simpa only [Pi.smul_apply, smul_eq_mul] using hx
    _ = fun x => c * cubeIncrement Q k f x := cubeIncrement_smul Q k f c

theorem energy_eq_lp_norm_sq
    (Q : TriadicCube 2) (f : Lp ℝ 2 (normalizedCubeMeasure Q)) :
    energy Q (fun x => f x) = ‖f‖ ^ 2 := by
  rw [energy_eq_cubeLpNorm_sq Q (Lp.memLp f)]
  unfold Homogenization.cubeLpNorm
  rw [Lp.norm_def]

noncomputable def cubeIncrementToLp
    (Q : TriadicCube 2) (k : ℕ)
    (f : Lp ℝ 2 (normalizedCubeMeasure Q)) :
    Lp ℝ 2 (normalizedCubeMeasure Q) :=
  (increment_memLp Q k (fun x => f x)).toLp
    (cubeIncrement Q k (fun x => f x))

/-- A fixed Haar increment is a contraction on the normalized spatial L²
space. This makes each finite positive-Haar partial energy continuous under
strong L² convergence. -/
noncomputable def cubeIncrementL2CLM
    (Q : TriadicCube 2) (k : ℕ) :
    Lp ℝ 2 (normalizedCubeMeasure Q) →L[ℝ]
      Lp ℝ 2 (normalizedCubeMeasure Q) := by
  let A : Lp ℝ 2 (normalizedCubeMeasure Q) →ₗ[ℝ]
      Lp ℝ 2 (normalizedCubeMeasure Q) := {
    toFun := cubeIncrementToLp Q k
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [
        (increment_memLp Q k (fun x => (f + g) x)).coeFn_toLp,
        (increment_memLp Q k (fun x => f x)).coeFn_toLp,
        (increment_memLp Q k (fun x => g x)).coeFn_toLp,
        Lp.coeFn_add (cubeIncrementToLp Q k f)
          (cubeIncrementToLp Q k g)] with x hsum hf hg hout
      change cubeIncrementToLp Q k (f + g) x =
        (cubeIncrementToLp Q k f + cubeIncrementToLp Q k g) x
      change cubeIncrementToLp Q k (f + g) x = _ at hsum
      change cubeIncrementToLp Q k f x = _ at hf
      change cubeIncrementToLp Q k g x = _ at hg
      calc
        cubeIncrementToLp Q k (f + g) x =
            cubeIncrement Q k (fun y => (f + g) y) x := hsum
        _ = cubeIncrement Q k f x + cubeIncrement Q k g x :=
          congrFun (cubeIncrement_lp_add Q k f g) x
        _ = cubeIncrementToLp Q k f x + cubeIncrementToLp Q k g x := by
          rw [← hf, ← hg]
        _ = (cubeIncrementToLp Q k f + cubeIncrementToLp Q k g) x :=
          hout.symm
    map_smul' := by
      intro c f
      apply Lp.ext
      filter_upwards [
        (increment_memLp Q k (fun x => (c • f) x)).coeFn_toLp,
        (increment_memLp Q k (fun x => f x)).coeFn_toLp,
        Lp.coeFn_smul c (cubeIncrementToLp Q k f)] with x hscaled hf hout
      change cubeIncrementToLp Q k (c • f) x =
        (c • cubeIncrementToLp Q k f) x
      change cubeIncrementToLp Q k (c • f) x = _ at hscaled
      change cubeIncrementToLp Q k f x = _ at hf
      calc
        cubeIncrementToLp Q k (c • f) x =
            cubeIncrement Q k (fun y => (c • f) y) x := hscaled
        _ = c * cubeIncrement Q k f x :=
          congrFun (cubeIncrement_lp_smul Q k c f) x
        _ = c * cubeIncrementToLp Q k f x := by rw [← hf]
        _ = (c • cubeIncrementToLp Q k f) x := hout.symm
  }
  refine LinearMap.mkContinuous A 1 ?_
  intro f
  change ‖cubeIncrementToLp Q k f‖ ≤ 1 * ‖f‖
  have henergy : energy Q (cubeIncrement Q k (fun x => f x)) ≤
      energy Q (fun x => f x) := by
    cases k with
    | zero =>
        simpa only [cubeIncrement_zero] using
          energy_projection_le Q 0 (Lp.memLp f)
    | succ k =>
        rw [energy_increment_succ Q k (Lp.memLp f)]
        have htop := energy_projection_le Q (k + 1) (Lp.memLp f)
        have hbottom : 0 ≤ energy Q (cubeProjection Q k (fun x => f x)) :=
          energy_nonneg Q _
        linarith
  have houtput : ‖cubeIncrementToLp Q k f‖ ^ 2 =
      energy Q (cubeIncrement Q k (fun x => f x)) := by
    rw [cubeIncrementToLp, Lp.norm_toLp,
      energy_eq_cubeLpNorm_sq Q (increment_memLp Q k (fun x => f x))]
    unfold Homogenization.cubeLpNorm
    rfl
  have hinput : energy Q (fun x => f x) = ‖f‖ ^ 2 :=
    energy_eq_lp_norm_sq Q f
  have hsquare : ‖cubeIncrementToLp Q k f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [houtput, ← hinput]
    exact henergy
  nlinarith [norm_nonneg (cubeIncrementToLp Q k f), norm_nonneg f]

theorem cubeIncrementL2CLM_apply
    (Q : TriadicCube 2) (k : ℕ)
    (f : Lp ℝ 2 (normalizedCubeMeasure Q)) :
    cubeIncrementL2CLM Q k f = cubeIncrementToLp Q k f := by
  simp [cubeIncrementL2CLM, LinearMap.mkContinuous_apply]

theorem energy_cubeIncrement_eq_clm_norm_sq
    (Q : TriadicCube 2) (k : ℕ)
    (f : Lp ℝ 2 (normalizedCubeMeasure Q)) :
    energy Q (cubeIncrement Q k (fun x => f x)) =
      ‖cubeIncrementL2CLM Q k f‖ ^ 2 := by
  rw [cubeIncrementL2CLM_apply, cubeIncrementToLp, Lp.norm_toLp,
    energy_eq_cubeLpNorm_sq Q (increment_memLp Q k (fun x => f x))]
  unfold Homogenization.cubeLpNorm
  rfl

theorem partialEnergy_eq_l2_clm_sum
    (Q : TriadicCube 2) (q : ℝ) (N : ℕ)
    (f : Lp ℝ 2 (normalizedCubeMeasure Q)) :
    partialEnergy Q q N (fun x => f x) =
      ∑ k ∈ Finset.range (N + 1),
        q ^ k * ‖cubeIncrementL2CLM Q k f‖ ^ 2 := by
  rw [partialEnergy]
  apply Finset.sum_congr rfl
  intro k hk
  rw [energy_cubeIncrement_eq_clm_norm_sq]

/-- Every fixed finite positive-Haar partial energy is continuous in the
normalized spatial L² representative. -/
theorem partialEnergy_tendsto_of_l2_tendsto
    (Q : TriadicCube 2) (q : ℝ) (N : ℕ)
    (fseq : ℕ → Lp ℝ 2 (normalizedCubeMeasure Q))
    (f : Lp ℝ 2 (normalizedCubeMeasure Q))
    (hseq : Tendsto fseq atTop (𝓝 f)) :
    Tendsto
      (fun n => partialEnergy Q q N (fun x => fseq n x)) atTop
      (𝓝 (partialEnergy Q q N (fun x => f x))) := by
  let F : Lp ℝ 2 (normalizedCubeMeasure Q) → ℝ := fun g =>
    ∑ k ∈ Finset.range (N + 1),
      q ^ k * ‖cubeIncrementL2CLM Q k g‖ ^ 2
  have hF : Continuous F := by
    dsimp [F]
    apply continuous_finsetSum
    intro k hk
    exact continuous_const.mul
      (((cubeIncrementL2CLM Q k).continuous.norm).pow 2)
  have hrepr (g : Lp ℝ 2 (normalizedCubeMeasure Q)) :
      partialEnergy Q q N (fun x => g x) = F g := by
    exact partialEnergy_eq_l2_clm_sum Q q N g
  have hseqEq : (fun n => partialEnergy Q q N (fun x => fseq n x)) =
      fun n => F (fseq n) := by
    funext n
    exact hrepr (fseq n)
  rw [hseqEq, hrepr f]
  exact (hF.tendsto f).comp hseq

/-- Every finite Haar partial energy of an H¹ field is bounded by its full
positive Haar energy. The summability needed for this comparison follows from
cell Poincaré, with no separate Besov-domain premise. -/
theorem partialEnergy_le_positiveHaarNorm_sq_of_h1
    (Q : TriadicCube 2) {f : Vec 2 → ℝ} {G : Vec 2 → Vec 2}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hw : HasWeakGradientOn (openCubeSet Q) f G) (N : ℕ) :
    partialEnergy Q (Real.sqrt 3) N f ≤ positiveHaarNorm Q f ^ 2 := by
  let q : ℝ := Real.sqrt 3
  let S : ℝ := ∑ i : Fin 2, energy Q (fun x => G x i)
  have hq0 : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hq1 : 1 < q := by
    dsimp [q]
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hq9 : q / 9 < 1 := by
    dsimp [q]
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have huL2 : MemL2On (openCubeSet Q) f :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf
  have hGL2 : GradMemL2On (openCubeSet Q) G := fun i =>
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q (hG i)
  let C : ℝ := cubeScaleFactor Q ^ 2 / Real.pi ^ 2 * S
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgeom : Summable (fun j : ℕ => C * (q / 9) ^ j) :=
    (summable_geometric_of_lt_one (by positivity) hq9).mul_left C
  have hres : Summable (fun j : ℕ => q ^ j *
      energy Q (fun x => f x - cubeProjection Q j f x)) := by
    apply hgeom.of_norm_bounded
    intro j
    rw [Real.norm_eq_abs]
    have hcell := cell_poincare_of_weakGradient Q j huL2 hGL2 hw
    have hnonneg : 0 ≤ q ^ j *
        energy Q (fun x => f x - cubeProjection Q j f x) :=
      mul_nonneg (pow_nonneg hq0.le _) (energy_nonneg Q _)
    rw [abs_of_nonneg hnonneg]
    have hcell' : energy Q (fun x => f x - cubeProjection Q j f x) ≤
        cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) * S := by
      simpa [S, mul_comm, mul_left_comm, mul_assoc] using hcell
    calc
      q ^ j * energy Q (fun x => f x - cubeProjection Q j f x) ≤
          q ^ j * (cubeScaleFactor Q ^ 2 / (9 ^ j * Real.pi ^ 2) * S) :=
        mul_le_mul_of_nonneg_left hcell' (pow_nonneg hq0.le _)
      _ = C * (q / 9) ^ j := by
        dsimp [C]
        rw [div_pow]
        field_simp [pow_ne_zero j (by norm_num : (9 : ℝ) ≠ 0)]
  have hinc := summable_primal_increments_of_residuals Q q hf hres
  have htail0 (j : ℕ) : 0 ≤ q ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) f) :=
    mul_nonneg (pow_nonneg hq0.le _) (energy_nonneg Q _)
  have htail := hinc.sum_le_tsum (Finset.range N) (fun j hj => htail0 j)
  have hpartial : partialEnergy Q q N f = energy Q (cubeIncrement Q 0 f) +
      ∑ j ∈ Finset.range N, q ^ (j + 1) *
        energy Q (cubeIncrement Q (j + 1) f) := by
    rw [partialEnergy, Finset.sum_range_succ']
    simp only [pow_zero, one_mul]
    ring
  have hprimal0 : 0 ≤ primalEnergy Q q f := by
    unfold primalEnergy
    apply add_nonneg (energy_nonneg Q _)
    apply tsum_nonneg
    intro j
    exact htail0 j
  calc
    partialEnergy Q q N f = energy Q (cubeIncrement Q 0 f) +
        ∑ j ∈ Finset.range N, q ^ (j + 1) *
          energy Q (cubeIncrement Q (j + 1) f) := hpartial
    _ ≤ energy Q (cubeIncrement Q 0 f) +
        ∑' j, q ^ (j + 1) * energy Q (cubeIncrement Q (j + 1) f) :=
      add_le_add le_rfl htail
    _ = primalEnergy Q q f := rfl
    _ = positiveHaarNorm Q f ^ 2 := by
      rw [positiveHaarNorm, Real.sq_sqrt hprimal0]

end ASDExplicitGamma.Scalar
