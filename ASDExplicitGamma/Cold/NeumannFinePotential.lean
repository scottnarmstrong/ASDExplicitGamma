module

public import ASDExplicitGamma.Cold.SquareVectorEnergy
public import ASDExplicitGamma.Triadic.PlanarNeumannBridge

/-! # Fine projected potentials from cell orthogonality and the square Hessian identity -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic ASDExplicitGamma.Triadic.Torus
open scoped BigOperators ENNReal

namespace ASDExplicitGamma.Cold

/-- The sharp fine-potential estimate for every finite family of cosine coefficients.
The only cancellation premise is the actual depth-r cell projection of the vector source. -/
theorem neumann_fine_finite_coeff_bound (Q : TriadicCube 2) (r : ℕ)
    {G : Vec 2 → Vec 2} (hG : ∀ j,
      MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q))
    (hprojection : ∀ i, cubeProjection Q r (fun x => G x i) = 0)
    {w : H1Function (openCubeSet Q)}
    (hw : ASDExplicitGamma.Triadic.Support.Localization.IsNeumannPrimitive Q G w)
    (S : Finset (Fin 2 → ℕ)) (hS : ∀ q ∈ S, q ≠ 0) :
    ∑ q ∈ S, modeMult q *
        (∫ x, cubeCos Q (natVec q) x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2 ≤
      cubeScaleFactor Q ^ 2 / (9 ^ r * Real.pi ^ 2) * squareVectorEnergy Q G := by
  classical
  let coeff : (Fin 2 → ℕ) → ℝ := fun q =>
    ∫ x, cubeCos Q (natVec q) x * w.toFun x ∂normalizedCubeMeasure Q
  let β : (Fin 2 → ℕ) → ℝ := fun q =>
    modeMult q * coeff q / cubeEig Q (natVec q)
  let V : Vec 2 → Vec 2 := fun x j => testField Q S β j x
  let A : ℝ := ∑ q ∈ S, modeMult q * coeff q ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun q _ => mul_nonneg (modeMult_pos q).le (sq_nonneg _)
  have hEig : ∀ q ∈ S, cubeEig Q (natVec q) ≠ 0 := by
    intro q hq
    exact (cubeEig_natVec_pos Q (hS q hq)).ne'
  have hDual : A = vectorPairing Q V G := by
    calc
      (∑ q ∈ S, modeMult q * coeff q ^ 2) =
          ∑ j : Fin 2, pairing Q (fun x => G x j) (testField Q S β j) := by
            rw [Finset.sum_congr rfl fun j _ => pairing_testField Q S β j (hG j),
              Finset.sum_comm]
            refine Finset.sum_congr rfl fun q hq => ?_
            have hid := neumann_coeff_identity Q hG hw (natVec q)
            have h1 : ∑ j : Fin 2,
                (-(β q) * cubeFreq Q (natVec q) j) *
                  ∫ x, cubeSin Q j (natVec q) x * G x j ∂normalizedCubeMeasure Q =
                -(β q) * ∑ j : Fin 2, cubeFreq Q (natVec q) j *
                  ∫ x, cubeSin Q j (natVec q) x * G x j ∂normalizedCubeMeasure Q := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              ring
            rw [h1, ← neg_neg (∑ j : Fin 2, cubeFreq Q (natVec q) j *
              ∫ x, cubeSin Q j (natVec q) x * G x j ∂normalizedCubeMeasure Q), ← hid]
            dsimp [β, coeff]
            field_simp [hEig q hq]
      _ = vectorPairing Q V G := by
            unfold vectorPairing
            dsimp [V]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [pairing_comm]
  have hF : ∀ j, MemLp (fun x => V x j) 2 (normalizedCubeMeasure Q) := by
    intro j
    change MemLp (testField Q S β j) 2 (normalizedCubeMeasure Q)
    exact memLp_testField Q S β j
  let Vres : Vec 2 → Vec 2 := fun x j => V x j - cubeProjection Q r (fun y => V y j) x
  have hVres (j : Fin 2) : MemLp (fun x => Vres x j) 2 (normalizedCubeMeasure Q) :=
    (hF j).sub (projection_memLp Q r (fun x => V x j) 2)
  have hDualRes : A = vectorPairing Q Vres G := by
    rw [hDual]
    unfold vectorPairing
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [Vres]
    rw [pairing_sub_left Q (hF j) (projection_memLp Q r _ 2) (hG j),
      projection_selfAdjoint Q r (hF j) (hG j), hprojection j]
    simp [pairing, cubeAverage_eq_integral_normalizedCubeMeasure]
  have hHess : ∑ q ∈ S, β q ^ 2 * cubeEig Q (natVec q) ^ 2 / modeMult q = A := by
    dsimp [A, coeff, β]
    apply Finset.sum_congr rfl
    intro q hq
    have hm := (modeMult_pos q).ne'
    field_simp [hEig q hq, hm]
  have hCell (j : Fin 2) : energy Q (fun x => Vres x j) ≤
      cubeScaleFactor Q ^ 2 / (9 ^ r * Real.pi ^ 2) *
        ∑ i : Fin 2, energy Q (testHess Q S β j i) := by
    have h := cell_poincare_of_weakGradient Q r
      (neumannTestFieldH1 Q S β j).memL2
      (neumannTestFieldH1 Q S β j).gradMemL2
      (neumannTestFieldH1 Q S β j).hasWeakGradient
    simpa only [Vres, V, neumannTestFieldH1_toFun, neumannTestFieldH1_grad] using h
  have hResidual : squareVectorEnergy Q Vres ≤
      cubeScaleFactor Q ^ 2 / (9 ^ r * Real.pi ^ 2) * A := by
    unfold squareVectorEnergy
    calc
      _ ≤ ∑ j : Fin 2, cubeScaleFactor Q ^ 2 / (9 ^ r * Real.pi ^ 2) *
          ∑ i : Fin 2, energy Q (testHess Q S β j i) := Finset.sum_le_sum (fun j _ => hCell j)
      _ = _ := by rw [← Finset.mul_sum, sum_energy_testHess, hHess]
  have hC : 0 ≤ cubeScaleFactor Q ^ 2 / (9 ^ r * Real.pi ^ 2) := by positivity
  have hEG := squareVectorEnergy_nonneg Q G
  have hER := squareVectorEnergy_nonneg Q Vres
  have hAupper : A ≤ Real.sqrt (squareVectorEnergy Q Vres) * Real.sqrt (squareVectorEnergy Q G) :=
    (by rw [hDualRes]; exact (le_abs_self _).trans (abs_squareVectorPairing_le Q hVres hG))
  have hAsq : A ^ 2 ≤ squareVectorEnergy Q Vres * squareVectorEnergy Q G := by
    have h := pow_le_pow_left₀ hA hAupper 2
    rwa [mul_pow, Real.sq_sqrt hER, Real.sq_sqrt hEG] at h
  have hfinal : A ^ 2 ≤ cubeScaleFactor Q ^ 2 / (9 ^ r * Real.pi ^ 2) * A * squareVectorEnergy Q G :=
    hAsq.trans (mul_le_mul_of_nonneg_right hResidual hEG)
  change A ≤ cubeScaleFactor Q ^ 2 / (9 ^ r * Real.pi ^ 2) * squareVectorEnergy Q G
  by_cases hAzero : A = 0
  · rw [hAzero]
    exact mul_nonneg hC hEG
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    have hmul : A * A ≤
        (cubeScaleFactor Q ^ 2 / (9 ^ r * Real.pi ^ 2) * squareVectorEnergy Q G) * A := by
      nlinarith only [hfinal]
    exact le_of_mul_le_mul_right hmul hApos

/-- Full L² control of a fine projected potential, from actual cell orthogonality. -/
theorem neumann_fine_L2_bridge_sq (Q : TriadicCube 2) (r : ℕ)
    {G : Vec 2 → Vec 2} (hG : ∀ j,
      MemLp (fun x => G x j) 2 (normalizedCubeMeasure Q))
    (hprojection : ∀ i, cubeProjection Q r (fun x => G x i) = 0)
    {w : H1Function (openCubeSet Q)}
    (hw : ASDExplicitGamma.Triadic.Support.Localization.IsNeumannPrimitive Q G w) :
    energy Q w.toFun ≤ cubeScaleFactor Q ^ 2 / (9 ^ r * Real.pi ^ 2) * squareVectorEnergy Q G := by
  classical
  let coeff : (Fin 2 → ℕ) → ℝ := fun q =>
    ∫ x, cubeCos Q (natVec q) x * w.toFun x ∂normalizedCubeMeasure Q
  have hwL : MemLp w.toFun 2 (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On w.memL2
  have hParseval : HasSum
      (fun p : Fin 2 → ℤ =>
        (∫ x, cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2)
      (∫ x, w.toFun x ^ 2 ∂normalizedCubeMeasure Q) := by
    have huB : MemLp w.toFun 2 (boxMeasure (cubeCorner Q) (cubeScaleFactor Q)) := by
      rw [boxMeasure_eq_normalizedCubeMeasure]
      exact hwL
    have h := hasSum_sq_boxCoeff_cos (cubeCorner Q) (cubeScaleFactor_pos' Q) huB
    rw [boxMeasure_eq_normalizedCubeMeasure] at h
    exact h
  have hzero : coeff 0 = 0 := by
    dsimp [coeff]
    simp only [cubeCos_natVec_zero, one_mul]
    rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
    exact hw.1
  rw [energy_eq_integral_sq, ← hParseval.tsum_eq]
  refine Real.tsum_le_of_sum_le (fun p => sq_nonneg _) fun T => ?_
  calc
    ∑ p ∈ T,
        (∫ x, cubeCos Q p x * w.toFun x ∂normalizedCubeMeasure Q) ^ 2
        = ∑ p ∈ T, coeff (natAbsVec p) ^ 2 := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [cubeCos_natAbsVec Q p]
    _ ≤ ∑ q ∈ T.image natAbsVec, modeMult q * coeff q ^ 2 :=
          sum_le_sum_image_natAbsVec T (fun q => coeff q ^ 2) (fun q => sq_nonneg _)
    _ = ∑ q ∈ (T.image natAbsVec).erase 0, modeMult q * coeff q ^ 2 := by
          exact (Finset.sum_erase _ (by simp [hzero])).symm
    _ ≤ cubeScaleFactor Q ^ 2 / (9 ^ r * Real.pi ^ 2) * squareVectorEnergy Q G := by
          simpa only [coeff] using
            neumann_fine_finite_coeff_bound Q r hG hprojection hw ((T.image natAbsVec).erase 0)
              (fun q hq => Finset.ne_of_mem_erase hq)

end ASDExplicitGamma.Cold
