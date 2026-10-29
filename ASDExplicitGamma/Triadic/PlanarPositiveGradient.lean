module

public import ASDExplicitGamma.Triadic.PoincareCell
public import ASDExplicitGamma.Triadic.PlanarConstants
public import ASDExplicitGamma.Triadic.VectorHaar
public import Homogenization.Sobolev.Foundations.CubePoisson.Solver

/-! Exact positive-Haar control from the cube Poincare inequality. -/

@[expose] public section

noncomputable section

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Triadic

/-- The positive Haar increment series converges for an `H¹` function. The
sharp cell Poincaré estimate gives a geometric majorant with ratio
`√3 / 9 < 1`. -/
theorem positiveHaarIncrementSeries_summable (Q : TriadicCube 2)
    {f : Vec 2 → ℝ} {G : Vec 2 → Vec 2}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hw : HasWeakGradientOn (openCubeSet Q) f G) :
    Summable (fun k : ℕ => (Real.sqrt 3) ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) f)) := by
  let q : ℝ := Real.sqrt 3
  let R : ℝ := cubeScaleFactor Q
  let S : ℝ := ∑ i, energy Q (fun x => G x i)
  have hq0 : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hq9 : q / 9 < 1 := by
    dsimp [q]
    nlinarith [Real.sqrt_nonneg (3 : ℝ),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have hR : 0 < R := by dsimp [R]; exact cubeScaleFactor_pos' Q
  have hC : 0 ≤ R ^ 2 / Real.pi ^ 2 * S :=
    mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)) hS
  have hgeom : Summable (fun k : ℕ => q * (R ^ 2 / Real.pi ^ 2 * S) *
      (q / 9) ^ k) :=
    (summable_geometric_of_lt_one (by positivity) hq9).mul_left
      (q * (R ^ 2 / Real.pi ^ 2 * S))
  have huL2 : MemL2On (openCubeSet Q) f :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf
  have hGL2 : GradMemL2On (openCubeSet Q) G := fun i =>
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q (hG i)
  apply hgeom.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs]
  have hnonneg : 0 ≤ q ^ (k + 1) *
      energy Q (cubeIncrement Q (k + 1) f) :=
    mul_nonneg (pow_nonneg hq0.le _) (energy_nonneg Q _)
  rw [abs_of_nonneg hnonneg]
  have hinc : energy Q (cubeIncrement Q (k + 1) f) ≤
      energy Q (fun x => f x - cubeProjection Q k f x) := by
    rw [energy_increment_succ Q k hf, energy_residual Q k hf]
    linarith [energy_projection_le Q (k + 1) hf]
  have hcell := cell_poincare_of_weakGradient Q k huL2 hGL2 hw
  have hgeomEq : q ^ (k + 1) *
      (R ^ 2 / (9 ^ k * Real.pi ^ 2) * S) =
        q * (R ^ 2 / Real.pi ^ 2 * S) * (q / 9) ^ k := by
    rw [pow_succ, div_pow]
    dsimp [R]
    field_simp
  calc
    q ^ (k + 1) * energy Q (cubeIncrement Q (k + 1) f)
        ≤ q ^ (k + 1) * (R ^ 2 / (9 ^ k * Real.pi ^ 2) * S) :=
          mul_le_mul_of_nonneg_left (hinc.trans hcell) (pow_nonneg hq0.le _)
    _ = q * (R ^ 2 / Real.pi ^ 2 * S) * (q / 9) ^ k := hgeomEq

/-- The weighted Haar residual series of an `H¹` scalar field converges.
The sharp cell Poincaré estimate bounds its terms by a geometric series with
ratio `√3 / 9`. -/
theorem positiveHaarResidualSeries_summable (Q : TriadicCube 2)
    {f : Vec 2 → ℝ} {G : Vec 2 → Vec 2}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hw : HasWeakGradientOn (openCubeSet Q) f G) :
    Summable (fun j : ℕ => (Real.sqrt 3) ^ j *
      energy Q (fun x => f x - cubeProjection Q j f x)) := by
  let q : ℝ := Real.sqrt 3
  let R : ℝ := cubeScaleFactor Q
  let S : ℝ := ∑ i, energy Q (fun x => G x i)
  let C : ℝ := R ^ 2 / Real.pi ^ 2 * S
  have hq0 : 0 < q := Real.sqrt_pos.2 (by norm_num)
  have hq9 : q / 9 < 1 := by
    dsimp [q]
    nlinarith [Real.sqrt_nonneg (3 : ℝ),
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgeom : Summable (fun j : ℕ => C * (q / 9) ^ j) :=
    (summable_geometric_of_lt_one (by positivity) hq9).mul_left C
  have huL2 : MemL2On (openCubeSet Q) f :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf
  have hGL2 : GradMemL2On (openCubeSet Q) G := fun i =>
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q (hG i)
  apply hgeom.of_norm_bounded
  intro j
  rw [Real.norm_eq_abs]
  have hcell := cell_poincare_of_weakGradient Q j huL2 hGL2 hw
  have hnonneg : 0 ≤ q ^ j *
      energy Q (fun x => f x - cubeProjection Q j f x) :=
    mul_nonneg (pow_nonneg hq0.le _) (energy_nonneg Q _)
  rw [abs_of_nonneg hnonneg]
  have hres : energy Q (fun x => f x - cubeProjection Q j f x) ≤
      R ^ 2 / (9 ^ j * Real.pi ^ 2) * S := by
    simpa [S, R, mul_comm, mul_left_comm, mul_assoc] using hcell
  calc
    q ^ j * energy Q (fun x => f x - cubeProjection Q j f x) ≤
        q ^ j * (R ^ 2 / (9 ^ j * Real.pi ^ 2) * S) :=
          mul_le_mul_of_nonneg_left hres (pow_nonneg hq0.le _)
    _ = C * (q / 9) ^ j := by
          dsimp [C]
          rw [div_pow]
          field_simp [pow_ne_zero j (by norm_num : (9 : ℝ) ≠ 0)]


/-- The positive Haar norm of an `H¹` scalar field is bounded by its `L²`
size and the exact order-`1/4` weak-gradient size. This is the positive-norm
estimate used on the finite spectral Poisson fields in the Dirichlet bridge. -/
theorem positiveHaarNorm_sq_le_l2_add_gradient (Q : TriadicCube 2)
    {f : Vec 2 → ℝ} {G : Vec 2 → Vec 2}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hw : HasWeakGradientOn (openCubeSet Q) f G) :
    positiveHaarNorm Q f ^ 2 ≤
      energy Q f + cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
        ∑ i, energy Q (fun x => G x i) := by
  let q : ℝ := Real.sqrt 3
  let S : ℝ := ∑ i, energy Q (fun x => G x i)
  let R : ℝ := cubeScaleFactor Q
  have hq1 : 1 < q := by
    dsimp [q]
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hq0 : 0 < q := lt_trans zero_lt_one hq1
  have hq9 : q / 9 < 1 := by
    dsimp [q]
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hS : 0 ≤ S := by
    dsimp [S]
    exact Finset.sum_nonneg fun i _ => energy_nonneg Q _
  have hR : 0 < R := cubeScaleFactor_pos' Q
  have huL2 : MemL2On (openCubeSet Q) f :=
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf
  have hGL2 : GradMemL2On (openCubeSet Q) G := fun i =>
    memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q (hG i)
  have hres_summable : Summable (fun j : ℕ => q ^ j *
      energy Q (fun x => f x - cubeProjection Q j f x)) := by
    let C : ℝ := R ^ 2 / Real.pi ^ 2 * S
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hgeom : Summable (fun j : ℕ => C * (q / 9) ^ j) := by
      exact (summable_geometric_of_lt_one (by positivity) hq9).mul_left C
    apply hgeom.of_norm_bounded
    intro j
    rw [Real.norm_eq_abs]
    have hcell := cell_poincare_of_weakGradient Q j huL2 hGL2 hw
    have hnonneg : 0 ≤ q ^ j *
        energy Q (fun x => f x - cubeProjection Q j f x) :=
      mul_nonneg (pow_nonneg hq0.le _) (energy_nonneg Q _)
    rw [abs_of_nonneg hnonneg]
    have hgrad :
        energy Q (fun x => f x - cubeProjection Q j f x) ≤
          R ^ 2 / (9 ^ j * Real.pi ^ 2) * S := by
      simpa [S, R, mul_comm, mul_left_comm, mul_assoc] using hcell
    have hgeom_eq : q ^ j * (R ^ 2 / (9 ^ j * Real.pi ^ 2) * S) =
        C * (q / 9) ^ j := by
      dsimp [C]
      rw [div_pow]
      field_simp
    calc
      q ^ j * energy Q (fun x => f x - cubeProjection Q j f x)
          ≤ q ^ j * (R ^ 2 / (9 ^ j * Real.pi ^ 2) * S) :=
            mul_le_mul_of_nonneg_left hgrad (pow_nonneg hq0.le _)
      _ = C * (q / 9) ^ j := hgeom_eq
  have habel := primalEnergy_eq_abel Q hq1 hf hres_summable
  have hgeom_tsum :
      (∑' j : ℕ, q ^ j *
        energy Q (fun x => f x - cubeProjection Q j f x)) ≤
        (R ^ 2 / Real.pi ^ 2 * S) * (1 - q / 9)⁻¹ := by
    let C : ℝ := R ^ 2 / Real.pi ^ 2 * S
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hgeom : Summable (fun j : ℕ => C * (q / 9) ^ j) :=
      (summable_geometric_of_lt_one (by positivity) hq9).mul_left C
    have hterm : ∀ j, q ^ j *
        energy Q (fun x => f x - cubeProjection Q j f x) ≤ C * (q / 9) ^ j := by
      intro j
      have hcell := cell_poincare_of_weakGradient Q j huL2 hGL2 hw
      have hgrad :
          energy Q (fun x => f x - cubeProjection Q j f x) ≤
            R ^ 2 / (9 ^ j * Real.pi ^ 2) * S := by
        simpa [S, R, mul_comm, mul_left_comm, mul_assoc] using hcell
      calc
        q ^ j * energy Q (fun x => f x - cubeProjection Q j f x)
            ≤ q ^ j * (R ^ 2 / (9 ^ j * Real.pi ^ 2) * S) :=
              mul_le_mul_of_nonneg_left hgrad (pow_nonneg hq0.le _)
        _ = C * (q / 9) ^ j := by
              dsimp [C]
              rw [div_pow]
              field_simp
    calc
      (∑' j : ℕ, q ^ j *
          energy Q (fun x => f x - cubeProjection Q j f x))
          ≤ ∑' j : ℕ, C * (q / 9) ^ j :=
            hres_summable.tsum_le_tsum hterm hgeom
      _ = C * ∑' j : ℕ, (q / 9) ^ j := by rw [tsum_mul_left]
      _ = C * (1 - q / 9)⁻¹ := by
            rw [tsum_geometric_of_lt_one (by positivity) hq9]
  have hc1 : planarC1 ^ 2 = (q - 1) / (Real.pi ^ 2 * (1 - q / 9)) := by
    simpa [q] using planarC1_sq
  have henergy :
      primalEnergy Q q f ≤ energy Q f + R ^ 2 * planarC1 ^ 2 * S := by
    rw [habel]
    have hcoef : (q - 1) * (R ^ 2 / Real.pi ^ 2 * S) * (1 - q / 9)⁻¹ =
        R ^ 2 * planarC1 ^ 2 * S := by
      rw [hc1]
      field_simp
    have hqcoef : 0 ≤ q - 1 := by linarith
    calc
      energy Q f + (q - 1) *
          ∑' j : ℕ, q ^ j *
            energy Q (fun x => f x - cubeProjection Q j f x)
          ≤ energy Q f + (q - 1) *
            ((R ^ 2 / Real.pi ^ 2 * S) * (1 - q / 9)⁻¹) := by
              exact add_le_add (le_refl (energy Q f))
                (mul_le_mul_of_nonneg_left hgeom_tsum hqcoef)
      _ = energy Q f + ((q - 1) * (R ^ 2 / Real.pi ^ 2 * S) *
          (1 - q / 9)⁻¹) := by congr 1; ring
      _ = energy Q f + R ^ 2 * planarC1 ^ 2 * S := by
            rw [hcoef]
  calc
    positiveHaarNorm Q f ^ 2 = primalEnergy Q q f := by
      rw [positiveHaarNorm]
      change Real.sqrt (primalEnergy Q (Real.sqrt 3) f) ^ 2 = _
      rw [Real.sq_sqrt (primalEnergy_nonneg Q (Real.sqrt 3)
        (Real.sqrt_nonneg 3) f)]
    _ ≤ energy Q f + R ^ 2 * planarC1 ^ 2 * S := henergy
    _ = energy Q f + cubeScaleFactor Q ^ 2 * planarC1 ^ 2 *
        ∑ i, energy Q (fun x => G x i) := by rfl

end ASDExplicitGamma.Triadic

end
