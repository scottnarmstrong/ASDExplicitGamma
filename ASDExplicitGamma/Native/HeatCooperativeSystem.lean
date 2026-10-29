module

public import ASDExplicitGamma.Native.AugmentedMomentSystems
public import ASDExplicitGamma.Numerics.Native.TaylorBound
public import Mathlib.Algebra.Ring.Ext
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import ASDExplicitGamma.Native.HeatInitialMoments
public import ASDExplicitGamma.Numerics.Native.MatrixReplay

/-! A configured native moment flow is bounded by its exact positive replay. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Set Matrix MeasureTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Gaussian

/-- The diagonal scaling in the producer's 153 systems keeps the exact
interpolated NATIVE_START vector: row `k` is the upward-rounded value of
`r^(k-1) / z^k`, where `r` is the twentieth-root interpolation constant. -/
theorem nativeConfiguredSystem_startVector_formula (j : Fin 153) (i : Fin 21) :
    (nativeConfiguredSystem j).system.v.getD i.val 0 =
      nativeUp
        ((nativeRootUp ((7 / 2 : ℚ)^20) 19)^(i.val - 1) /
          (nativeConfiguredSystem j).system.z^i.val) := by
  decide +kernel +revert

/-- Every producer scaling is strictly positive, so its moment coordinates can
be unscaled and compared with the exact NATIVE_START interpolation bounds. -/
theorem nativeConfiguredSystem_scale_pos (j : Fin 153) :
    0 < (nativeConfiguredSystem j).system.z := by
  decide +kernel +revert

/-- Hölder's exact `L¹`/`L²⁰` interpolation profile is below the root rounded
in every producer start vector. -/
theorem nativeStart_holder_profile_le (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    ((21 / 100 : ℝ)^20)^(((k : ℝ) - 1) / 19) *
      (3 / 50 : ℝ)^((20 - (k : ℝ)) / 19) ≤
    (3 / 50 : ℝ)^k *
      (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1) := by
  let α : ℝ := ((k : ℝ) - 1) / 19
  let β : ℝ := (20 - (k : ℝ)) / 19
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk20R : (k : ℝ) ≤ 20 := by exact_mod_cast hk20
  have hα : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg (sub_nonneg.mpr hk1R) (by norm_num)
  have hβ : 0 ≤ β := by
    dsimp [β]
    exact div_nonneg (sub_nonneg.mpr hk20R) (by norm_num)
  have hexp : 20 * α + β = (k : ℝ) := by
    dsimp [α, β]
    ring
  have hA : (21 / 100 : ℝ) = (3 / 50 : ℝ) * (7 / 2 : ℝ) := by norm_num
  have hpowA : ((((3 / 50 : ℝ) * (7 / 2 : ℝ))^20)^α) =
      ((3 / 50 : ℝ) * (7 / 2 : ℝ))^(20 * α) := by
    rw [← Real.rpow_natCast ((3 / 50 : ℝ) * (7 / 2 : ℝ)) 20]
    exact (Real.rpow_mul (x := (3 / 50 : ℝ) * (7 / 2 : ℝ))
      (by positivity) (20 : ℝ) α).symm
  have hpowB : (7 / 2 : ℝ)^(20 * α) = ((7 / 2 : ℝ)^20)^α := by
    rw [← Real.rpow_natCast (7 / 2 : ℝ) 20]
    exact Real.rpow_mul (x := (7 / 2 : ℝ)) (by positivity) (20 : ℝ) α
  have hscale :
      ((21 / 100 : ℝ)^20)^α * (3 / 50 : ℝ)^β =
        (3 / 50 : ℝ)^k * ((7 / 2 : ℝ)^20)^α := by
    rw [hA]
    calc
      (((3 / 50 : ℝ) * (7 / 2 : ℝ))^20)^α * (3 / 50 : ℝ)^β =
          ((3 / 50 : ℝ) * (7 / 2 : ℝ))^(20 * α) *
            (3 / 50 : ℝ)^β := by rw [hpowA]
      _ = ((3 / 50 : ℝ)^(20 * α) * (7 / 2 : ℝ)^(20 * α)) *
            (3 / 50 : ℝ)^β := by
              rw [Real.mul_rpow (by norm_num) (by norm_num)]
      _ = (3 / 50 : ℝ)^(20 * α + β) * (7 / 2 : ℝ)^(20 * α) := by
            calc
              _ = ((3 / 50 : ℝ)^(20 * α) * (3 / 50 : ℝ)^β) *
                    (7 / 2 : ℝ)^(20 * α) := by ring
              _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3 / 50)]
      _ = (3 / 50 : ℝ)^k * ((7 / 2 : ℝ)^20)^α := by
            rw [hexp, Real.rpow_natCast (3 / 50 : ℝ) k]
            rw [hpowB]
  have hrootValid : nativeRootValid ((7 / 2 : ℚ)^20) 19 = true := by
    decide +kernel
  have hrootQ := (of_decide_eq_true hrootValid).2.2.2
  have hrootNonnegQ := (of_decide_eq_true hrootValid).2.2.1
  have hbaseCast : (7 / 2 : ℝ)^20 =
      (((7 / 2 : ℚ)^20 : ℚ) : ℝ) := by norm_num
  have hrootCast : (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^19 =
      ((nativeRootUp ((7 / 2 : ℚ)^20) 19 ^ 19 : ℚ) : ℝ) := by norm_num
  have hroot : (7 / 2 : ℝ)^20 ≤
      (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^19 := by
    rw [hbaseCast, hrootCast]
    exact_mod_cast hrootQ
  have hrootNonneg :
      0 ≤ (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ) := by
    exact_mod_cast hrootNonnegQ
  have hrootPow : ((7 / 2 : ℝ)^20)^α ≤
      (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1) := by
    calc
      ((7 / 2 : ℝ)^20)^α ≤
          ((nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^19)^α :=
        Real.rpow_le_rpow (by positivity) hroot hα
      _ = (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(19 * α) := by
        rw [← Real.rpow_natCast _ 19]
        exact (Real.rpow_mul
          (x := (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)) hrootNonneg 19 α).symm
      _ = _ := by
        have hkcast : (19 : ℝ) * α = ((k - 1 : ℕ) : ℝ) := by
          dsimp [α]
          rw [Nat.cast_sub hk1]
          ring
        rw [hkcast, Real.rpow_natCast]
  calc
    ((21 / 100 : ℝ)^20)^(((k : ℝ) - 1) / 19) *
        (3 / 50 : ℝ)^((20 - (k : ℝ)) / 19) =
      ((21 / 100 : ℝ)^20)^α * (3 / 50 : ℝ)^β := by rfl
    _ = (3 / 50 : ℝ)^k * ((7 / 2 : ℝ)^20)^α := hscale
    _ ≤ (3 / 50 : ℝ)^k *
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1) := by
      exact mul_le_mul_of_nonneg_left hrootPow (by positivity)

/-- The NATIVE_START mean and twentieth-root caps give the exact interpolated
moment bound used in each producer vector. -/
theorem nativeStartMoment_integral_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ)
    (h20 : eLpNorm f 20 μ ≤ ENNReal.ofReal (21 / 100 : ℝ))
    (hfirst : ∫⁻ ω, ‖f ω‖ₑ ∂μ ≤ ENNReal.ofReal (3 / 50 : ℝ))
    (k : ℕ) (hk1 : 1 ≤ k) (hk20 : k ≤ 20) :
    (∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ).toReal ≤
      (3 / 50 : ℝ)^k *
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1) := by
  let α : ℝ := ((k : ℝ) - 1) / 19
  let β : ℝ := (20 - (k : ℝ)) / 19
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hk20R : (k : ℝ) ≤ 20 := by exact_mod_cast hk20
  have hα : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg (sub_nonneg.mpr hk1R) (by norm_num)
  have hβ : 0 ≤ β := by
    dsimp [β]
    exact div_nonneg (sub_nonneg.mpr hk20R) (by norm_num)
  have hholder := lintegral_enorm_natPow_le_holder20_of_caps
    hf k hk1 hk20 h20 hfirst
  have hholder' :
      (∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ) ≤
        ((ENNReal.ofReal (21 / 100 : ℝ) ^ (20 : ℝ)) ^ α) *
          (ENNReal.ofReal (3 / 50 : ℝ)) ^ β := by
    simpa [α, β] using hholder
  have hholderEq :
      ((ENNReal.ofReal (21 / 100 : ℝ) ^ (20 : ℝ)) ^ α) *
          (ENNReal.ofReal (3 / 50 : ℝ)) ^ β =
        ENNReal.ofReal (((21 / 100 : ℝ)^(20 : ℝ))^α *
          (3 / 50 : ℝ)^β) := by
    rw [ENNReal.ofReal_rpow_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 21 / 100) (by norm_num : (0 : ℝ) ≤ 20)]
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hα]
    rw [ENNReal.ofReal_rpow_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 3 / 50) hβ]
    rw [← ENNReal.ofReal_mul (by positivity)]
  have hfinite :
      ((ENNReal.ofReal (21 / 100 : ℝ) ^ (20 : ℝ)) ^ α) *
          (ENNReal.ofReal (3 / 50 : ℝ)) ^ β ≠ ⊤ := by
    rw [hholderEq]
    exact ENNReal.ofReal_ne_top
  calc
    (∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ).toReal ≤
        (((ENNReal.ofReal (21 / 100 : ℝ) ^ (20 : ℝ)) ^ α) *
          (ENNReal.ofReal (3 / 50 : ℝ)) ^ β).toReal :=
      ENNReal.toReal_mono hfinite hholder'
    _ = ((21 / 100 : ℝ)^(20 : ℝ))^α * (3 / 50 : ℝ)^β := by
      rw [hholderEq]
      simp
      positivity
    _ = ((21 / 100 : ℝ)^20)^α * (3 / 50 : ℝ)^β := by
      exact congrArg (fun x : ℝ => x^α * (3 / 50 : ℝ)^β)
        (Real.rpow_natCast (21 / 100 : ℝ) 20)
    _ ≤ (3 / 50 : ℝ)^k *
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(k - 1) :=
      nativeStart_holder_profile_le k hk1 hk20

noncomputable section

local instance nativeHeatDuhamelMatrixRing (n : ℕ) :
    NormedRing (Matrix (Fin n) (Fin n) ℝ) := Matrix.linftyOpNormedRing
local instance nativeHeatDuhamelMatrixAlgebra (n : ℕ) :
    NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℝ) := Matrix.linftyOpNormedAlgebra

private def nativeHeatMatrixEntryLinear {n : ℕ} (i j : Fin n) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
  { toFun := fun A => A i j
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

private noncomputable def nativeHeatMatrixEntryCLM {n : ℕ} (i j : Fin n) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  (nativeHeatMatrixEntryLinear i j).toContinuousLinearMap

private theorem nativeHeatMatrixEntryCLM_apply {n : ℕ} (i j : Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) : nativeHeatMatrixEntryCLM i j A = A i j := rfl

private theorem nativeHeatMatrixExpEntry_hasDerivAt {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (i j : Fin n) :
    @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s : ℝ => NormedSpace.exp (s • G) i j)
      ((NormedSpace.exp (t • G) * G) i j) t := by
  have h := (nativeHeatMatrixEntryCLM i j).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const G t)
  have h' : @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun s : ℝ => nativeHeatMatrixEntryCLM i j (NormedSpace.exp (s • G)))
      (nativeHeatMatrixEntryCLM i j (NormedSpace.exp (t • G) * G)) t := by
    convert h using 1 <;> rfl
  simpa only [nativeHeatMatrixEntryCLM_apply] using h'

private theorem nativeHeatMatrixExpEntry_hasDerivAt_standard {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (s • G) i j)
      ((NormedSpace.exp (t • G) * G) i j) t := by
  have hmodule : (RCLike.toInnerProductSpaceReal.toModule : Module ℝ ℝ) =
      (inferInstance : Module ℝ ℝ) := by
    apply Module.ext
    rfl
  have hadd : (Real.normedAddCommGroup.toAddCommGroup : AddCommGroup ℝ) =
      (inferInstance : AddCommGroup ℝ) := rfl
  simpa only [hmodule, hadd] using nativeHeatMatrixExpEntry_hasDerivAt G t i j

private theorem nativeHeatMatrixExpTimeEntry_hasDerivAt {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (t s : ℝ) (i j : Fin n) :
    HasDerivAt (fun x : ℝ => NormedSpace.exp ((t - x) • G) i j)
      (-(NormedSpace.exp ((t - s) • G) * G) i j) s := by
  have hparam : HasDerivAt (fun x : ℝ => t - x) (-1) s := by
    convert (hasDerivAt_const s t).sub (hasDerivAt_id s) using 1
    · funext x
      rfl
    · ring
  have h := (nativeHeatMatrixExpEntry_hasDerivAt_standard G (t - s) i j).comp s hparam
  convert h using 1
  · rfl
  · ring

private theorem nativeHeatMatrixPow_nonneg {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j) (k : ℕ) :
    ∀ i j, 0 ≤ (G ^ k) i j := by
  induction k with
  | zero =>
      intro i j
      simp only [pow_zero]
      rw [Matrix.one_apply]
      split_ifs <;> norm_num
  | succ k ih =>
      intro i j
      rw [pow_succ]
      simp only [Matrix.mul_apply]
      exact Finset.sum_nonneg fun l _ => mul_nonneg (ih i l) (hG l j)

private theorem nativeHeatMatrixExp_nonneg {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : ∀ i j, 0 ≤ G i j)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ i j, 0 ≤ NormedSpace.exp (t • G) i j := by
  intro i j
  have hGt : ∀ a b, 0 ≤ (t • G) a b := by
    intro a b
    simpa using mul_nonneg ht (hG a b)
  have hterm (k : ℕ) :
      0 ≤ (((t • G) ^ k *ᵥ (Pi.single j (1 : ℝ))) i) /
        (Nat.factorial k : ℝ) := by
    apply div_nonneg
    · rw [Matrix.mulVec_single_one]
      exact nativeHeatMatrixPow_nonneg (t • G) hGt k i j
    · positivity
  have hs := ASDExplicitGamma.Numerics.Native.native_matrix_exp_hasSum
    (t • G) (Pi.single j (1 : ℝ)) i
  have hsum : 0 ≤ ∑' k : ℕ,
      (((t • G) ^ k *ᵥ (Pi.single j (1 : ℝ))) i) /
        (Nat.factorial k : ℝ) := tsum_nonneg hterm
  have hentry : (∑' k : ℕ,
      (((t • G) ^ k *ᵥ (Pi.single j (1 : ℝ))) i) /
        (Nat.factorial k : ℝ)) = NormedSpace.exp (t • G) i j := by
    calc
      _ = (NormedSpace.exp (t • G) *ᵥ (Pi.single j (1 : ℝ))) i := hs.tsum_eq
      _ = _ := by rw [Matrix.mulVec_single_one]; rfl
  rw [← hentry]
  exact hsum

private theorem nativeHeatMatrixExpAction_hasDerivAt {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • G) *ᵥ v) i)
      (((NormedSpace.exp (t • G) * G) *ᵥ v) i) t := by
  have hterms (j : Fin n) :
      HasDerivAt (fun s : ℝ => NormedSpace.exp (s • G) i j * v j)
        ((NormedSpace.exp (t • G) * G) i j * v j) t :=
    (nativeHeatMatrixExpEntry_hasDerivAt_standard G t i j).mul_const (v j)
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun j _ => hterms j)
  have hfun : (fun s : ℝ => (NormedSpace.exp (s • G) *ᵥ v) i) =
      fun s => ∑ j ∈ Finset.univ, NormedSpace.exp (s • G) i j * v j := by
    funext s
    rw [Matrix.mulVec_apply_eq_sum]
  have hderiv :
      (∑ j ∈ Finset.univ, (NormedSpace.exp (t • G) * G) i j * v j) =
        ((NormedSpace.exp (t • G) * G) *ᵥ v) i := by
    rw [Matrix.mulVec_apply_eq_sum]
  rw [hfun]
  convert hsum using 1
  · funext s
    simp
  · exact hderiv

private theorem nativeHeatMatrixExpAction_monotoneOn {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hG : ∀ i j, 0 ≤ G i j) (hv : ∀ j, 0 ≤ v j) (i : Fin n) :
    MonotoneOn (fun t => (NormedSpace.exp (t • G) *ᵥ v) i) (Icc (0 : ℝ) 1) := by
  have hd : Differentiable ℝ (fun t : ℝ => (NormedSpace.exp (t • G) *ᵥ v) i) := by
    intro t
    exact (nativeHeatMatrixExpAction_hasDerivAt G v t i).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    hd.continuous.continuousOn hd.differentiableOn
  intro t ht
  have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa [interior_Icc] using ht
  have ht0 : 0 ≤ t := le_of_lt ht'.1
  change 0 ≤ deriv (fun s => (NormedSpace.exp (s • G) *ᵥ v) i) t
  rw [(nativeHeatMatrixExpAction_hasDerivAt G v t i).deriv]
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_nonneg
  intro j hj
  apply mul_nonneg
  rw [Matrix.mul_apply]
  · exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (nativeHeatMatrixExp_nonneg G hG ht0 i k) (hG k j)
  · exact hv j

private noncomputable def nativeHeatFrozenTimeProduct {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (u : ℝ → Fin n → ℝ)
    (t : ℝ) (i : Fin n) (s : ℝ) : ℝ :=
  Finset.univ.sum fun j : Fin n => NormedSpace.exp ((t - s) • G) i j * u s j

private theorem nativeHeatFrozenTimeProduct_hasDerivAt {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (u : ℝ → Fin n → ℝ)
    (hdiff : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ j, DifferentiableAt ℝ (fun x => u x j) s)
    (t s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (i : Fin n) :
    HasDerivAt (nativeHeatFrozenTimeProduct G u t i)
      (Finset.univ.sum fun j : Fin n =>
        (-(NormedSpace.exp ((t - s) • G) * G) i j) * u s j +
          NormedSpace.exp ((t - s) • G) i j * deriv (fun x => u x j) s) s := by
  have hterms (j : Fin n) : HasDerivAt
      (fun x : ℝ => NormedSpace.exp ((t - x) • G) i j * u x j)
      ((-(NormedSpace.exp ((t - s) • G) * G) i j) * u s j +
        NormedSpace.exp ((t - s) • G) i j * deriv (fun x => u x j) s) s :=
    (nativeHeatMatrixExpTimeEntry_hasDerivAt G t s i j).mul (hdiff s hs j).hasDerivAt
  have hsum := HasDerivAt.sum (u := Finset.univ) (fun j _ => hterms j)
  have hfun : nativeHeatFrozenTimeProduct G u t i = fun x =>
      ∑ j ∈ Finset.univ,
        NormedSpace.exp ((t - x) • G) i j * u x j := by
    funext x
    simp [nativeHeatFrozenTimeProduct]
  rw [hfun]
  convert hsum using 1
  · funext x
    simp

private theorem nativeHeatFrozenTimeProduct_deriv_formula {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (u : ℝ → Fin n → ℝ)
    (hdiff : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ j, DifferentiableAt ℝ (fun x => u x j) s)
    (t s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) (i : Fin n) :
    deriv (nativeHeatFrozenTimeProduct G u t i) s =
      (NormedSpace.exp ((t - s) • G) *ᵥ
        (fun j => deriv (fun x => u x j) s - (G *ᵥ u s) j)) i := by
  have hderiv := (nativeHeatFrozenTimeProduct_hasDerivAt G u hdiff t s hs i).deriv
  rw [hderiv]
  let A := NormedSpace.exp ((t - s) • G)
  let du : Fin n → ℝ := fun j => deriv (fun x => u x j) s
  let gu : Fin n → ℝ := G *ᵥ u s
  change (∑ j : Fin n, (-(A * G) i j * (u s) j + A i j * du j)) =
    (A *ᵥ fun j => du j - gu j) i
  have hneg : (∑ j : Fin n, (-((A * G) i j)) * (u s) j) =
      -((A * G) *ᵥ (u s)) i := by
    rw [Matrix.mulVec_apply_eq_sum]
    rw [← Finset.sum_neg_distrib]
    congr 1
    funext j
    ring
  have hpos : (∑ j : Fin n, A i j * du j) = (A *ᵥ du) i := by
    rw [Matrix.mulVec_apply_eq_sum]
  have hright : (A *ᵥ fun j => du j - gu j) i =
      (A *ᵥ du) i - (A *ᵥ gu) i := by
    simp only [Matrix.mulVec_apply_eq_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hmul : (A * G) *ᵥ (u s) = A *ᵥ gu := by simp [gu]
  calc
    _ = -((A * G) *ᵥ (u s)) i + (A *ᵥ du) i := by
      rw [Finset.sum_add_distrib, hneg, hpos]
    _ = (A *ᵥ du) i - (A *ᵥ gu) i := by rw [hmul]; ring
    _ = (A *ᵥ fun j => du j - gu j) i := hright.symm

/-- Duhamel comparison on the heat interval needs only continuity up to the
initial time and differentiability in the open interval. This matches GA-HEAT,
which supplies a right derivative at zero rather than global differentiability. -/
theorem nativeHeatDuhamelComparisonOn {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℝ) (u : ℝ → Fin n → ℝ) (v : Fin n → ℝ)
    (hG : ∀ i j, 0 ≤ G i j)
    (hcont : ∀ i, ContinuousOn (fun t => u t i) (Icc (0 : ℝ) 1))
    (hdiff : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i, DifferentiableAt ℝ (fun s => u s i) t)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i,
      deriv (fun s => u s i) t ≤ (G *ᵥ u t) i)
    (hinit : ∀ i, u 0 i ≤ v i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin n) :
    u t i ≤ (NormedSpace.exp (t • G) *ᵥ v) i := by
  let f : ℝ → ℝ := nativeHeatFrozenTimeProduct G u t i
  have hfcont : ContinuousOn f (Icc (0 : ℝ) t) := by
    have hkernel (j : Fin n) : ContinuousOn
        (fun s : ℝ => NormedSpace.exp ((t - s) • G) i j) (Icc (0 : ℝ) t) := by
      have hcontExp : Continuous (fun s : ℝ => NormedSpace.exp ((t - s) • G) i j) := by
        rw [continuous_iff_continuousAt]
        intro s
        exact (nativeHeatMatrixExpTimeEntry_hasDerivAt G t s i j).continuousAt
      exact hcontExp.continuousOn
    have hu (j : Fin n) : ContinuousOn (fun s : ℝ => u s j) (Icc (0 : ℝ) t) :=
      (hcont j).mono (by intro s hs; exact ⟨hs.1, hs.2.trans ht1⟩)
    have hterm (j : Fin n) : ContinuousOn
        (fun s : ℝ => NormedSpace.exp ((t - s) • G) i j * u s j)
        (Icc (0 : ℝ) t) := (hkernel j).mul (hu j)
    change ContinuousOn (fun s : ℝ => ∑ j : Fin n,
      NormedSpace.exp ((t - s) • G) i j * u s j) (Icc (0 : ℝ) t)
    exact continuousOn_finsetSum Finset.univ (fun j hj => hterm j)
  have hfDiff : DifferentiableOn ℝ f (interior (Icc (0 : ℝ) t)) := by
    intro s hs
    have hs' : s ∈ Ioo (0 : ℝ) t := by simpa [interior_Icc] using hs
    have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs'.1, lt_of_lt_of_le hs'.2 ht1⟩
    exact (nativeHeatFrozenTimeProduct_hasDerivAt G u hdiff t s hs01 i).differentiableAt.differentiableWithinAt
  have hfmono : AntitoneOn f (Icc (0 : ℝ) t) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) t) hfcont hfDiff
    intro s hs
    have hs' : s ∈ Ioo (0 : ℝ) t := by simpa [interior_Icc] using hs
    have hs01 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs'.1, lt_of_lt_of_le hs'.2 ht1⟩
    have hts : 0 ≤ t - s := sub_nonneg.mpr hs'.2.le
    rw [nativeHeatFrozenTimeProduct_deriv_formula G u hdiff t s hs01 i]
    rw [Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_nonpos
    intro j hj
    apply mul_nonpos_of_nonneg_of_nonpos
    · exact nativeHeatMatrixExp_nonneg G hG hts i j
    · exact sub_nonpos.mpr (hderiv s hs01 j)
  have hle : f t ≤ f 0 := hfmono ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
  have hleft : f t = u t i := by
    simp [f, nativeHeatFrozenTimeProduct, Matrix.one_apply]
  have hright : f 0 = (NormedSpace.exp (t • G) *ᵥ u 0) i := by
    simp [f, nativeHeatFrozenTimeProduct, Matrix.mulVec_apply_eq_sum]
  have hflow : u t i ≤ (NormedSpace.exp (t • G) *ᵥ u 0) i := by
    simpa [hleft, hright] using hle
  calc
    u t i ≤ (NormedSpace.exp (t • G) *ᵥ u 0) i := hflow
    _ ≤ (NormedSpace.exp (t • G) *ᵥ v) i := by
      rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (hinit j)
        (nativeHeatMatrixExp_nonneg G hG ht0 i j)

/-- The configured replay also accepts the regularity supplied by GA-HEAT:
continuity on the closed time interval and differentiability only in its
interior.  The endpoint comparison uses monotonicity of the positive matrix
flow, so no derivative at either endpoint is needed. -/
theorem nativeConfiguredHeatFlow_le_replay_on (j : Fin 153)
    (u : ℝ → Fin 21 → ℝ)
    (hCont : ∀ i : Fin 21, ContinuousOn (fun t => u t i) (Icc (0 : ℝ) 1))
    (hDiffAt : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i : Fin 21,
      DifferentiableAt ℝ (fun s => u s i) t)
    (hDeriv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i : Fin 21,
      deriv (fun s => u s i) t ≤
        (nativeSystemMatrix (nativeConfiguredSystem j).system *ᵥ u t) i)
    (hfixed : ∀ t ∈ Icc (0 : ℝ) 1, u t 0 = 1)
    (hStartRest : ∀ i : Fin 21, i.val ≠ 0 →
      u 0 i ≤ nativeVectorReal (nativeConfiguredSystem j).system.v i)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 21) :
    u t i ≤ nativeVectorReal (nativeConfiguredSystem j).result i := by
  let G := nativeSystemMatrix (nativeConfiguredSystem j).system
  let v := nativeVectorReal (nativeConfiguredSystem j).system.v
  have hG : ∀ a b, 0 ≤ G a b := by
    simpa [G] using augmentedMomentMatrix_nonneg j
  have hv : ∀ a, 0 ≤ v a := by
    intro a
    dsimp [v, nativeVectorReal]
    exact_mod_cast ((augmentedMomentSystem_bounds j).1 a).1
  have hinit : ∀ a, u 0 a ≤ v a := by
    intro a
    by_cases ha : a.val = 0
    · have ha0 : a = 0 := Fin.ext ha
      subst a
      have hu0 : u 0 0 = 1 := hfixed 0 ⟨le_rfl, by norm_num⟩
      have hv0 : v 0 = 1 := by
        dsimp [v, nativeVectorReal]
        rw [augmentedMomentSystem_first_coordinate]
        norm_num
      rw [hu0, hv0]
    · exact hStartRest a ha
  have hflow := nativeHeatDuhamelComparisonOn G u v hG hCont hDiffAt
    hDeriv hinit ht0 ht1 i
  have hmono := nativeHeatMatrixExpAction_monotoneOn G v hG hv i
  have htime : (NormedSpace.exp (t • G) *ᵥ v) i ≤
      (NormedSpace.exp ((1 : ℝ) • G) *ᵥ v) i :=
    hmono ⟨ht0, ht1⟩ (by simp) ht1
  calc
    u t i ≤ (NormedSpace.exp (t • G) *ᵥ v) i := hflow
    _ ≤ (NormedSpace.exp G *ᵥ v) i := by simpa using htime
    _ ≤ nativeVectorReal (nativeConfiguredSystem j).result i := by
      simpa [G, v] using augmentedMomentSystem_replay j i

/-- The source's normalized moment curve: row zero is fixed at one, and the
positive degree rows divide the raw moments by the configured `a^k z^k` scale. -/
noncomputable def nativeConfiguredNormalizedMomentCurve (j : Fin 153)
    (moments : ℝ → Fin 21 → ℝ) : ℝ → Fin 21 → ℝ := fun t i =>
  if i.val = 0 then 1 else
    moments t i /
      ((3 / 50 : ℝ)^i.val * ((nativeConfiguredSystem j).system.z : ℝ)^i.val)

/-- The augmented coordinate of the normalized moment curve is identically one. -/
theorem nativeConfiguredNormalizedMomentCurve_fixed (j : Fin 153)
    (moments : ℝ → Fin 21 → ℝ) (t : ℝ) :
    nativeConfiguredNormalizedMomentCurve j moments t 0 = 1 := by
  simp [nativeConfiguredNormalizedMomentCurve]

/-- The producer's raw moment scale in degree `i`: the native mean cap is
`3/50`, and `z` is the system's positive diagonal rescaling parameter. -/
noncomputable def nativeConfiguredMomentScale (j : Fin 153) (i : Fin 21) : ℝ :=
  (3 / 50 : ℝ)^i.val * ((nativeConfiguredSystem j).system.z : ℝ)^i.val

theorem nativeConfiguredMomentScale_pos (j : Fin 153) (i : Fin 21) :
    0 < nativeConfiguredMomentScale j i := by
  unfold nativeConfiguredMomentScale
  have hz : (0 : ℝ) < ((nativeConfiguredSystem j).system.z : ℝ) := by
    exact_mod_cast nativeConfiguredSystem_scale_pos j
  positivity

/-- One step in the raw moment scale matches the predecessor coefficient in
the producer's augmented matrix. -/
theorem nativeConfiguredMomentScale_eq_predecessor (j : Fin 153) (i : Fin 21)
    (hi : i.val ≠ 0) :
    nativeConfiguredMomentScale j i =
      (3 / 50 : ℝ) * ((nativeConfiguredSystem j).system.z : ℝ) *
        nativeConfiguredMomentScale j (nativePrevious i) := by
  unfold nativeConfiguredMomentScale
  have hprev : (nativePrevious i).val = i.val - 1 := rfl
  rw [hprev]
  have hpow : i.val - 1 + 1 = i.val := by omega
  have ha : (3 / 50 : ℝ)^i.val =
      (3 / 50 : ℝ)^(i.val - 1) * (3 / 50 : ℝ) := by
    conv_lhs => rw [← hpow]
    rw [pow_succ]
  have hz : ((nativeConfiguredSystem j).system.z : ℝ)^i.val =
      ((nativeConfiguredSystem j).system.z : ℝ)^(i.val - 1) *
        ((nativeConfiguredSystem j).system.z : ℝ) := by
    conv_lhs => rw [← hpow]
    rw [pow_succ]
  rw [ha, hz]
  ring

theorem nativeConfiguredNormalizedMomentCurve_deriv_eq (j : Fin 153)
    (moments : ℝ → Fin 21 → ℝ) (i : Fin 21) (hi : i.val ≠ 0) (t : ℝ) :
    deriv (fun s => nativeConfiguredNormalizedMomentCurve j moments s i) t =
      deriv (fun s => moments s i) t / nativeConfiguredMomentScale j i := by
  simp [nativeConfiguredNormalizedMomentCurve, nativeConfiguredMomentScale, hi]

/-- The normalized moment curve preserves interior differentiability when the
raw source supplies differentiability only at positive times. -/
theorem nativeConfiguredNormalizedMomentCurve_differentiableAt_on
    (j : Fin 153) (moments : ℝ → Fin 21 → ℝ)
    (hDiffAt : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i : Fin 21,
      DifferentiableAt ℝ (fun s => moments s i) t) :
    ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i : Fin 21,
      DifferentiableAt ℝ
        (fun s => nativeConfiguredNormalizedMomentCurve j moments s i) t := by
  intro t ht i
  by_cases hi : i.val = 0
  · have hi0 : i = 0 := Fin.ext hi
    subst i
    simp [nativeConfiguredNormalizedMomentCurve]
  · simp [nativeConfiguredNormalizedMomentCurve, hi]
    exact (hDiffAt t ht i).div_const _

/-- The raw recurrence yields the configured matrix inequality on the open
heat interval, which is the interval of ordinary derivatives supplied by
GA-HEAT. -/
theorem nativeConfiguredNormalizedMomentCurve_deriv_le_of_raw_on
    (j : Fin 153) (moments : ℝ → Fin 21 → ℝ)
    (hFixed : ∀ t ∈ Icc (0 : ℝ) 1, moments t 0 = 1)
    (hRaw : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i : Fin 21, i.val ≠ 0 →
      deriv (fun s => moments s i) t ≤
        ((nativeConfiguredSystem j).system.diag.getD i.val 0 : ℝ) * moments t i +
        ((nativeConfiguredSystem j).system.subdiag.getD i.val 0 : ℝ) *
          ((3 / 50 : ℝ) * ((nativeConfiguredSystem j).system.z : ℝ)) *
          moments t (nativePrevious i) +
        ((nativeConfiguredSystem j).system.force.getD i.val 0 : ℝ) *
          nativeConfiguredMomentScale j i) :
    ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i : Fin 21,
      deriv (fun s => nativeConfiguredNormalizedMomentCurve j moments s i) t ≤
        (nativeSystemMatrix (nativeConfiguredSystem j).system *ᵥ
          nativeConfiguredNormalizedMomentCurve j moments t) i := by
  intro t ht i
  by_cases hi : i.val = 0
  · have hi0 : i = 0 := Fin.ext hi
    subst i
    rw [nativeSystemMatrix_mulVec]
    simp [nativeConfiguredNormalizedMomentCurve]
  · have hscalePos := nativeConfiguredMomentScale_pos j i
    have hprevPos := nativeConfiguredMomentScale_pos j (nativePrevious i)
    have hazPos : (0 : ℝ) < (3 / 50 : ℝ) *
        ((nativeConfiguredSystem j).system.z : ℝ) := by
      have hz : (0 : ℝ) < ((nativeConfiguredSystem j).system.z : ℝ) := by
        exact_mod_cast nativeConfiguredSystem_scale_pos j
      positivity
    have hzPos : (0 : ℝ) < ((nativeConfiguredSystem j).system.z : ℝ) := by
      exact_mod_cast nativeConfiguredSystem_scale_pos j
    have hscale := nativeConfiguredMomentScale_eq_predecessor j i hi
    have hcurrent : nativeConfiguredNormalizedMomentCurve j moments t i =
        moments t i / nativeConfiguredMomentScale j i := by
      simp [nativeConfiguredNormalizedMomentCurve, hi, nativeConfiguredMomentScale]
    have hprevious :
        nativeConfiguredNormalizedMomentCurve j moments t (nativePrevious i) =
          moments t (nativePrevious i) /
            nativeConfiguredMomentScale j (nativePrevious i) := by
      by_cases hp0 : (nativePrevious i).val = 0
      · have hp : nativePrevious i = 0 := Fin.ext hp0
        rw [hp]
        simp [nativeConfiguredNormalizedMomentCurve, nativeConfiguredMomentScale,
          hFixed t ⟨ht.1.le, ht.2.le⟩]
      · simp [nativeConfiguredNormalizedMomentCurve, nativeConfiguredMomentScale, hp0]
    have hconvert :
        (((nativeConfiguredSystem j).system.diag.getD i.val 0 : ℝ) * moments t i +
          ((nativeConfiguredSystem j).system.subdiag.getD i.val 0 : ℝ) *
            ((3 / 50 : ℝ) * ((nativeConfiguredSystem j).system.z : ℝ)) *
            moments t (nativePrevious i) +
          ((nativeConfiguredSystem j).system.force.getD i.val 0 : ℝ) *
            nativeConfiguredMomentScale j i) / nativeConfiguredMomentScale j i =
        ((nativeConfiguredSystem j).system.diag.getD i.val 0 : ℝ) *
            (moments t i / nativeConfiguredMomentScale j i) +
          ((nativeConfiguredSystem j).system.subdiag.getD i.val 0 : ℝ) *
            (moments t (nativePrevious i) /
              nativeConfiguredMomentScale j (nativePrevious i)) +
          ((nativeConfiguredSystem j).system.force.getD i.val 0 : ℝ) := by
      rw [hscale]
      field_simp [ne_of_gt hscalePos, ne_of_gt hprevPos, ne_of_gt hazPos,
        ne_of_gt hzPos, (by norm_num : (3 / 50 : ℝ) ≠ 0)]
    have hraw := hRaw t ht i hi
    have hrawDiv := div_le_div_of_nonneg_right hraw hscalePos.le
    rw [← nativeConfiguredNormalizedMomentCurve_deriv_eq j moments i hi t] at hrawDiv
    rw [hconvert] at hrawDiv
    calc
      deriv (fun s => nativeConfiguredNormalizedMomentCurve j moments s i) t ≤
          ((nativeConfiguredSystem j).system.diag.getD i.val 0 : ℝ) *
              (moments t i / nativeConfiguredMomentScale j i) +
            ((nativeConfiguredSystem j).system.subdiag.getD i.val 0 : ℝ) *
              (moments t (nativePrevious i) /
                nativeConfiguredMomentScale j (nativePrevious i)) +
            ((nativeConfiguredSystem j).system.force.getD i.val 0 : ℝ) := hrawDiv
      _ = (nativeSystemMatrix (nativeConfiguredSystem j).system *ᵥ
          nativeConfiguredNormalizedMomentCurve j moments t) i := by
        rw [nativeSystemMatrix_mulVec]
        simp [hi, hcurrent, hprevious,
          nativeConfiguredNormalizedMomentCurve_fixed]

/-- The raw-moment cooperative-system assembly with GA-HEAT's closed-interval
continuity and open-interval derivative interfaces. -/
theorem nativeConfiguredNormalizedMomentCurve_le_replay_of_raw_on
    (j : Fin 153) (moments : ℝ → Fin 21 → ℝ)
    (hCont : ∀ i : Fin 21, ContinuousOn (fun t => moments t i) (Icc (0 : ℝ) 1))
    (hDiffAt : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i : Fin 21,
      DifferentiableAt ℝ (fun s => moments s i) t)
    (hFixed : ∀ t ∈ Icc (0 : ℝ) 1, moments t 0 = 1)
    (hRaw : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i : Fin 21, i.val ≠ 0 →
      deriv (fun s => moments s i) t ≤
        ((nativeConfiguredSystem j).system.diag.getD i.val 0 : ℝ) * moments t i +
        ((nativeConfiguredSystem j).system.subdiag.getD i.val 0 : ℝ) *
          ((3 / 50 : ℝ) * ((nativeConfiguredSystem j).system.z : ℝ)) *
          moments t (nativePrevious i) +
        ((nativeConfiguredSystem j).system.force.getD i.val 0 : ℝ) *
          nativeConfiguredMomentScale j i)
    (hMoment : ∀ i : Fin 21, i.val ≠ 0 →
      moments 0 i ≤ (3 / 50 : ℝ)^i.val *
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(i.val - 1))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin 21) :
    nativeConfiguredNormalizedMomentCurve j moments t i ≤
      nativeVectorReal (nativeConfiguredSystem j).result i := by
  let u := nativeConfiguredNormalizedMomentCurve j moments
  have hcont : ∀ a : Fin 21, ContinuousOn (fun s => u s a) (Icc (0 : ℝ) 1) := by
    intro a
    by_cases ha : a.val = 0
    · have ha0 : a = 0 := Fin.ext ha
      subst a
      exact continuousOn_const
    · simp [u, nativeConfiguredNormalizedMomentCurve, ha]
      exact (hCont a).div_const _
  have hdiff : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ a : Fin 21,
      DifferentiableAt ℝ (fun r => u r a) s := by
    intro s hs a
    simpa [u] using
      (nativeConfiguredNormalizedMomentCurve_differentiableAt_on j moments
        hDiffAt s hs a)
  have hderiv := nativeConfiguredNormalizedMomentCurve_deriv_le_of_raw_on
    j moments hFixed hRaw
  have hfixed : ∀ s ∈ Icc (0 : ℝ) 1, u s 0 = 1 := by
    intro s hs
    exact nativeConfiguredNormalizedMomentCurve_fixed j moments s
  have hStartRest : ∀ a : Fin 21, a.val ≠ 0 →
      u 0 a ≤ nativeVectorReal (nativeConfiguredSystem j).system.v a := by
    intro a ha
    have haPos : 0 < (3 / 50 : ℝ)^a.val := by positivity
    have hzPos : 0 < ((nativeConfiguredSystem j).system.z : ℝ) := by
      exact_mod_cast nativeConfiguredSystem_scale_pos j
    have hzPow : 0 < ((nativeConfiguredSystem j).system.z : ℝ)^a.val := pow_pos hzPos _
    have hscaled : (moments 0 a / (3 / 50 : ℝ)^a.val) /
        ((nativeConfiguredSystem j).system.z : ℝ)^a.val ≤
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(a.val - 1) /
          ((nativeConfiguredSystem j).system.z : ℝ)^a.val := by
      apply div_le_div_of_nonneg_right _ hzPow.le
      apply (div_le_iff₀ haPos).2
      simpa [mul_comm] using hMoment a ha
    have hstart : u 0 a ≤
        (nativeRootUp ((7 / 2 : ℚ)^20) 19 : ℝ)^(a.val - 1) /
          ((nativeConfiguredSystem j).system.z : ℝ)^a.val := by
      calc
        u 0 a = (moments 0 a / (3 / 50 : ℝ)^a.val) /
            ((nativeConfiguredSystem j).system.z : ℝ)^a.val := by
          simp [u, nativeConfiguredNormalizedMomentCurve, ha]
          ring
        _ ≤ _ := hscaled
    have hround :
        (nativeRootUp ((7 / 2 : ℚ)^20) 19)^(a.val - 1) /
          (nativeConfiguredSystem j).system.z^a.val ≤
        nativeUp ((nativeRootUp ((7 / 2 : ℚ)^20) 19)^(a.val - 1) /
          (nativeConfiguredSystem j).system.z^a.val) := nativeUp_ge _
    have hrounded : u 0 a ≤
        (nativeUp ((nativeRootUp ((7 / 2 : ℚ)^20) 19)^(a.val - 1) /
          (nativeConfiguredSystem j).system.z^a.val) : ℝ) := by
      exact hstart.trans (by exact_mod_cast hround)
    have hformula := nativeConfiguredSystem_startVector_formula j a
    change u 0 a ≤ ((nativeConfiguredSystem j).system.v.getD a.val 0 : ℝ)
    rw [hformula]
    exact hrounded
  exact nativeConfiguredHeatFlow_le_replay_on j u hcont hdiff
    (by simpa [u] using hderiv) hfixed hStartRest ht0 ht1 i

end
end ASDExplicitGamma.Native
