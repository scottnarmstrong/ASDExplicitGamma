module

public import ASDExplicitGamma.Scalar.PairedTwoSlotLocal
public import ASDExplicitGamma.Inverse.PureFluxGeneratorForcedJoint

/-! The weak-Haar level summation for the two-slot paired forced estimate. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Inverse
open scoped BigOperators
noncomputable section

/-- Level energy of the source-shifted mean field. -/
noncomputable def shiftedLevel (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (V G : Vec 2 → Vec 2) (j : ℕ) : ℝ :=
  descendantsAverage Q j (fun R => vecNormSq
    ((fun i => cubeAverage R (fun x => V x i)) + forcedSource_feedback_shift Q j R hEll G))

/-- Weak energy of the source-shifted mean field. -/
noncomputable def shiftedWeak (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (V G : Vec 2 → Vec 2) : ℝ :=
  (1 - (Real.sqrt 3)⁻¹) * ∑' j : ℕ, (Real.sqrt 3)⁻¹ ^ j * shiftedLevel Q hEll V G j

theorem weak_shift_triangle (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    {V : Vec 2 → Vec 2}
    (hVcoord : ∀ i : Fin 2, MemLp (fun x => V x i) 2 (normalizedCubeMeasure Q))
    {G : Vec 2 → Vec 2} (hG : MemLp G 2 (normalizedCubeMeasure Q))
    (hGpos : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
      energy Q (cubeIncrement Q (j + 1) (fun x => G x i))))
    (hSseries : Summable (fun j : ℕ => (Real.sqrt 3)⁻¹ ^ j * shiftedLevel Q hEll V G j)) :
    Real.sqrt (vectorWeakHaarEnergy Q V) ≤ Real.sqrt (shiftedWeak Q hEll V G) +
      (3 : ℝ) ^ (-(1 / 4 : ℝ)) * lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ)) *
        Real.sqrt (forcedSourceCircleEnergy Q G) := by
  let U : Set (Vec 2) := openCubeSet Q
  let q : ℝ := Real.sqrt 3
  let w : ℝ := q⁻¹
  let H : ℝ := lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ))
  let meanV : TriadicCube 2 → Vec 2 := fun R i => cubeAverage R (fun x => V x i)
  let Vlevel : ℕ → ℝ := fun j => forcedSource_meanLevel Q j V
  let Slevel : ℕ → ℝ := fun j => descendantsAverage Q j (fun R =>
    vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll G))
  let Sweak : ℝ := (1 - w) * ∑' j : ℕ, w ^ j * Slevel j
  let Tweak : ℝ := (1 - w) * ∑' j : ℕ, w ^ j *
    forcedSource_feedback_shiftLevel Q j hEll G
  have hSweakEq : shiftedWeak Q hEll V G = Sweak := rfl
  rw [hSweakEq]
  have hq : 1 < q := by
    dsimp [q]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg (3 : ℝ)]
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : 0 ≤ 1 - w := by
    have hlt : w < 1 := (inv_lt_one₀ (by positivity)).2 hq
    linarith
  have hFvec : MemVectorL2 U G :=
    memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hG
  have hSnonneg (j : ℕ) : 0 ≤ Slevel j := by
    unfold Slevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  have hVSeries : Summable (fun j : ℕ => w ^ j * Vlevel j) := by
    simpa [w, q, Vlevel] using forcedSource_meanLevel_series_summable Q hVcoord
  have hVWeakEq : vectorWeakHaarEnergy Q V =
      (1 - w) * ∑' j : ℕ, w ^ j * Vlevel j := by
    simpa [w, q, Vlevel] using forcedSource_weakEnergy_eq_meanSeries Q hVcoord
  have hShiftData := forcedSource_feedback_shift_weakEnergy_le Q hEll hG hGpos
  have hTweakBound : Tweak ≤ w * H ^ 2 * forcedSourceCircleEnergy Q G := by
    simpa [Tweak, w, H, q] using hShiftData.2
  have hTweakNonneg : 0 ≤ Tweak := by
    dsimp [Tweak]
    apply mul_nonneg hw1
    apply tsum_nonneg
    intro j
    apply mul_nonneg (pow_nonneg hw j)
    unfold forcedSource_feedback_shiftLevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  let α : ℝ := (Real.sqrt (Real.sqrt 3))⁻¹
  have hαnonneg : 0 ≤ α := by dsimp [α]; positivity
  have hαsq : α ^ 2 = w := by
    dsimp [α, w, q]
    calc
      (Real.sqrt (Real.sqrt 3))⁻¹ ^ 2 =
          ((Real.sqrt (Real.sqrt 3)) ^ 2)⁻¹ := by rw [← inv_pow]
      _ = (Real.sqrt 3)⁻¹ := by rw [Real.sq_sqrt (Real.sqrt_nonneg 3)]
  have hαroot : Real.sqrt w = α := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg w) hαnonneg).1
    calc
      (Real.sqrt w) ^ 2 = w := Real.sq_sqrt hw
      _ = α ^ 2 := hαsq.symm
  have hTroot : Real.sqrt Tweak ≤ Real.sqrt w * H *
      Real.sqrt (forcedSourceCircleEnergy Q G) := by
    have hradEq : Real.sqrt (w * H ^ 2 * forcedSourceCircleEnergy Q G) =
        Real.sqrt w * H * Real.sqrt (forcedSourceCircleEnergy Q G) := by
      calc
        Real.sqrt (w * H ^ 2 * forcedSourceCircleEnergy Q G) =
            Real.sqrt (w * (H ^ 2 * forcedSourceCircleEnergy Q G)) := by ring_nf
        _ = Real.sqrt w * Real.sqrt (H ^ 2 * forcedSourceCircleEnergy Q G) :=
          Real.sqrt_mul hw _
        _ = Real.sqrt w * (Real.sqrt (H ^ 2) *
              Real.sqrt (forcedSourceCircleEnergy Q G)) := by
          rw [Real.sqrt_mul (sq_nonneg H)]
        _ = Real.sqrt w * H * Real.sqrt (forcedSourceCircleEnergy Q G) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
            (lemmaVInverseHistory_nonneg Q a
              (Real.one_lt_rpow (by norm_num) (by norm_num)))]
          ring
    rw [← hradEq]
    exact Real.sqrt_le_sqrt hTweakBound
  have hVsumSq (j : ℕ) : 0 ≤ (1 - w) * w ^ j * Vlevel j := by
    apply mul_nonneg (mul_nonneg hw1 (pow_nonneg hw j))
    unfold Vlevel forcedSource_meanLevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  have hSsumSq (j : ℕ) : 0 ≤ (1 - w) * w ^ j * Slevel j :=
    mul_nonneg (mul_nonneg hw1 (pow_nonneg hw j)) (hSnonneg j)
  have hTsumSq (j : ℕ) : 0 ≤ (1 - w) * w ^ j *
      forcedSource_feedback_shiftLevel Q j hEll G := by
    apply mul_nonneg (mul_nonneg hw1 (pow_nonneg hw j))
    unfold forcedSource_feedback_shiftLevel descendantsAverage
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro R hR
    exact vecNormSq_nonneg _
  let av : ℕ → ℝ := fun j => Real.sqrt ((1 - w) * w ^ j * Vlevel j)
  let as : ℕ → ℝ := fun j => Real.sqrt ((1 - w) * w ^ j * Slevel j)
  let aShift : ℕ → ℝ := fun j => Real.sqrt ((1 - w) * w ^ j *
    forcedSource_feedback_shiftLevel Q j hEll G)
  have hav : Summable (fun j : ℕ => (av j) ^ 2) := by
    have h := hVSeries.mul_left (1 - w)
    have heq : (fun j => (av j) ^ 2) =
        (fun j => (1 - w) * (w ^ j * Vlevel j)) := by
      funext j
      dsimp [av]
      rw [Real.sq_sqrt (hVsumSq j)]
      ring
    rw [heq]
    exact h
  have has : Summable (fun j : ℕ => (as j) ^ 2) := by
    have h := hSseries.mul_left (1 - w)
    have heq : (fun j => (as j) ^ 2) =
        (fun j => (1 - w) * (w ^ j * Slevel j)) := by
      funext j
      dsimp [as]
      rw [Real.sq_sqrt (hSsumSq j)]
      ring
    rw [heq]
    exact h
  have hShiftSeries : Summable (fun j : ℕ => w ^ j *
      forcedSource_feedback_shiftLevel Q j hEll G) := hShiftData.1
  have hat : Summable (fun j : ℕ => (aShift j) ^ 2) := by
    have h := hShiftSeries.mul_left (1 - w)
    have heq : (fun j => (aShift j) ^ 2) =
        (fun j => (1 - w) * (w ^ j *
          forcedSource_feedback_shiftLevel Q j hEll G)) := by
      funext j
      dsimp [aShift]
      rw [Real.sq_sqrt (hTsumSq j)]
      ring
    rw [heq]
    exact h
  have hLevelTriangle (j : ℕ) :
      Real.sqrt (Vlevel j) ≤ Real.sqrt (Slevel j) +
        Real.sqrt (forcedSource_feedback_shiftLevel Q j hEll G) := by
    have hagg := sqrt_descendantsAverage_energy_bound_three Q j
      (fun R => vecNormSq (meanV R))
      (fun R => vecNormSq (meanV R + forcedSource_feedback_shift Q j R hEll G))
      (fun R => vecNormSq (forcedSource_feedback_shift Q j R hEll G))
      (fun _ => 0) (A := 1) (B := 1) (C := 0)
      (by norm_num) (by norm_num) (by norm_num)
      (fun R hR => vecNormSq_nonneg _)
      (fun R hR => vecNormSq_nonneg _)
      (fun R hR => vecNormSq_nonneg _)
      (fun R hR => by simp)
      (fun R hR => by
        simpa using forcedSource_sqrt_vecNormSq_sub_le
          (meanV R) (forcedSource_feedback_shift Q j R hEll G))
    simpa [Vlevel, Slevel, forcedSource_meanLevel,
      forcedSource_feedback_shiftLevel] using hagg
  have hab (j : ℕ) : av j ≤ as j + aShift j := by
    have hc : 0 ≤ (1 - w) * w ^ j := mul_nonneg hw1 (pow_nonneg hw j)
    change Real.sqrt ((1 - w) * w ^ j * Vlevel j) ≤
      Real.sqrt ((1 - w) * w ^ j * Slevel j) +
        Real.sqrt ((1 - w) * w ^ j *
          forcedSource_feedback_shiftLevel Q j hEll G)
    calc
      Real.sqrt ((1 - w) * w ^ j * Vlevel j) =
          Real.sqrt ((1 - w) * w ^ j) * Real.sqrt (Vlevel j) :=
        Real.sqrt_mul hc _
      _ ≤ Real.sqrt ((1 - w) * w ^ j) *
          (Real.sqrt (Slevel j) +
            Real.sqrt (forcedSource_feedback_shiftLevel Q j hEll G)) :=
        mul_le_mul_of_nonneg_left (hLevelTriangle j) (Real.sqrt_nonneg _)
      _ = _ := by
        rw [Real.sqrt_mul hc, Real.sqrt_mul hc]
        ring
  have htriangle := sqrt_tsum_sq_le_of_pointwise
    (a := as) (b := aShift) (c := av) has hat
    (fun j => Real.sqrt_nonneg _) hab
  have havEq : (∑' j : ℕ, (av j) ^ 2) = vectorWeakHaarEnergy Q V := by
    calc
      _ = (1 - w) * ∑' j : ℕ, w ^ j * Vlevel j := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro j
        dsimp [av]
        rw [Real.sq_sqrt (hVsumSq j)]
        ring
      _ = vectorWeakHaarEnergy Q V := hVWeakEq.symm
  have hasEq : (∑' j : ℕ, (as j) ^ 2) = Sweak := by
    dsimp [Sweak]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp [as]
    rw [Real.sq_sqrt (hSsumSq j)]
    ring
  have hatEq : (∑' j : ℕ, (aShift j) ^ 2) = Tweak := by
    dsimp [Tweak]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    dsimp [aShift]
    rw [Real.sq_sqrt (hTsumSq j)]
    ring
  have hWeakTriangle : Real.sqrt (vectorWeakHaarEnergy Q V) ≤
      Real.sqrt Sweak + Real.sqrt Tweak := by
    rw [← havEq, ← hasEq, ← hatEq]
    exact htriangle.2
  have hroot : Real.sqrt (Real.sqrt 3) = (3 : ℝ) ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    calc
      ((3 : ℝ) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) =
          (3 : ℝ) ^ ((1 / 2 : ℝ) * (1 / 2 : ℝ)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) _ _).symm
      _ = (3 : ℝ) ^ (1 / 4 : ℝ) := by norm_num
  have hAlphaForm : (Real.sqrt (Real.sqrt 3))⁻¹ =
      (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), hroot]
  have hAlphaExact : α = (3 : ℝ) ^ (-(1 / 4 : ℝ)) := by
    simpa [α] using hAlphaForm
  have hShift : Real.sqrt Tweak ≤ α * H *
      Real.sqrt (forcedSourceCircleEnergy Q G) := by
    calc
      Real.sqrt Tweak ≤ Real.sqrt w * H *
          Real.sqrt (forcedSourceCircleEnergy Q G) := hTroot
      _ = α * H * Real.sqrt (forcedSourceCircleEnergy Q G) := by
        rw [hαroot]
  have hv := hWeakTriangle.trans (add_le_add le_rfl hShift)
  simpa only [hAlphaExact] using hv


end
end ASDExplicitGamma.Variational
