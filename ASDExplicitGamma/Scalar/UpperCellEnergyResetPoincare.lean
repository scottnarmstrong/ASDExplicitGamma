module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetBottomResidual
public import ASDExplicitGamma.Triadic.PlanarPositiveGradient
public import Mathlib.Analysis.Real.Pi.Bounds

/-! Centered positive-Haar control at the exact RESET quarter-power base. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Triadic
noncomputable section

/-- The exact centered RESET positive-Haar Poincare constant. -/
def upperCellResetPoincareConstant : ℝ :=
  sourceHaarBase/(Real.pi^2*(1-sourceHaarBase/9))

/-- A centered H1 scalar field has summable positive Haar increments and
its complete positive energy is controlled by its genuine weak gradient.
This proof uses the exact base q, not the larger square-root-three base. -/
theorem upper_cell_reset_centered_poincare
    (Q : TriadicCube 2) (q : ℝ) (hq0 : 0 ≤ q) (hq9 : q < 9)
    (f : Vec 2 → ℝ) (G : Vec 2 → Vec 2)
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hG : ∀ i,MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hw : HasWeakGradientOn (openCubeSet Q) f G) (hm : cubeAverage Q f=0) :
    Summable (fun j : ℕ => q^(j+1)*energy Q (cubeIncrement Q (j+1) f)) ∧
      primalEnergy Q q f ≤
        q/(Real.pi^2*(1-q/9))*cubeScaleFactor Q^2*
          ∑ i,energy Q (fun x => G x i) := by
  let C := cubeScaleFactor Q^2/Real.pi^2*∑ i,energy Q (fun x => G x i)
  have hr0 : 0 ≤ q/9 := div_nonneg hq0 (by norm_num)
  have hr1 : q/9 < 1 := (div_lt_one (by norm_num)).mpr hq9
  have hs := (summable_geometric_of_lt_one hr0 hr1).mul_left (q*C)
  have hb (j : ℕ) : q^(j+1)*energy Q (cubeIncrement Q (j+1) f) ≤
      q*C*(q/9)^j := by
    have hi : energy Q (cubeIncrement Q (j+1) f) ≤
        energy Q (fun x => f x-cubeProjection Q j f x) := by
      rw [energy_increment_succ Q j hf,energy_residual Q j hf]
      linarith [energy_projection_le Q (j+1) hf]
    have hc := cell_poincare_of_weakGradient Q j
      (memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hf)
      (fun i => memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q (hG i)) hw
    calc
      _ ≤ q^(j+1)*(cubeScaleFactor Q^2/(9^j*Real.pi^2)*
          ∑ i,energy Q (fun x => G x i)) :=
        mul_le_mul_of_nonneg_left (hi.trans hc) (pow_nonneg hq0 _)
      _ = q*C*(q/9)^j := by
        dsimp only [C]
        rw [pow_succ,div_pow]
        field_simp
  have ha := Summable.of_nonneg_of_le
    (fun j => mul_nonneg (pow_nonneg hq0 _) (energy_nonneg Q _)) hb hs
  refine ⟨ha,?_⟩
  unfold primalEnergy
  rw [cubeIncrement_zero,energy_projection_zero,hm,zero_pow (by norm_num : 2≠0),zero_add]
  calc
    _ ≤ ∑' j : ℕ,q*C*(q/9)^j := ha.tsum_le_tsum hb hs
    _ = q/(Real.pi^2*(1-q/9))*cubeScaleFactor Q^2*
        ∑ i,energy Q (fun x => G x i) := by
      rw [tsum_mul_left,tsum_geometric_of_lt_one hr0 hr1]
      dsimp only [C]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

/-- Source-quarter-power version of the exact centered gradient payment. -/
theorem upper_cell_reset_source_poincare
    (Q : TriadicCube 2) (f : Vec 2 → ℝ) (G : Vec 2 → Vec 2)
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hG : ∀ i,MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hw : HasWeakGradientOn (openCubeSet Q) f G) (hm : cubeAverage Q f=0) :
    Summable (fun j : ℕ => sourceHaarBase^(j+1)*energy Q (cubeIncrement Q (j+1) f)) ∧
      primalEnergy Q sourceHaarBase f ≤
        upperCellResetPoincareConstant*cubeScaleFactor Q^2*
          ∑ i,energy Q (fun x => G x i) := by
  have hq : sourceHaarBase < 9 := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3)
      (by norm_num : (1/4:ℝ)≤1)
    rw [Real.rpow_one] at hp
    exact hp.trans_lt (by norm_num)
  exact upper_cell_reset_centered_poincare Q sourceHaarBase
    (zero_le_one.trans source_haar_base_gt_one.le) hq f G hf hG hw hm

/-- A centered vector H1 source is admissible for the physical RESET bound;
its complete positive energy costs the exact gradient coefficient. -/
theorem upper_cell_reset_vector_poincare
    (Q : TriadicCube 2) (f : Vec 2 → Vec 2) (G : Vec 2 → Fin 2 → Vec 2)
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hG : ∀ i j,MemLp (fun x => G x i j) 2 (normalizedCubeMeasure Q))
    (hw : ∀ i,HasWeakGradientOn (openCubeSet Q) (fun x => f x i) (fun x => G x i))
    (hm : ∀ i,cubeAverage Q (fun x => f x i)=0) :
    ScalarPositiveHaarAdmissible Q f ∧
      positiveSourceEnergy Q f ≤ upperCellResetPoincareConstant*cubeScaleFactor Q^2*
        ∑ i,∑ j,energy Q (fun x => G x i j) := by
  have hc (i : Fin 2) : MemLp (fun x => f x i) 2 (normalizedCubeMeasure Q) :=
    (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ).comp_memLp' hf
  have hp (i : Fin 2) := upper_cell_reset_source_poincare Q (fun x => f x i)
    (fun x => G x i) (hc i) (hG i) (hw i) (hm i)
  refine ⟨⟨hf,fun i => (hp i).1⟩,?_⟩
  unfold positiveSourceEnergy
  calc
    _ ≤ ∑ i,upperCellResetPoincareConstant*cubeScaleFactor Q^2*
        ∑ j,energy Q (fun x => G x i j) := Finset.sum_le_sum (fun i _ => (hp i).2)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The Gaussian fourth-moment and physical derivative factors fit inside
the literal coefficient10 in the UPPER RESET profile. -/
theorem upper_cell_reset_poincare_payment :
    Real.sqrt 3*upperCellResetPoincareConstant*(156/5:ℝ) ≤ 10 := by
  have hq0 : 0 ≤ sourceHaarBase := zero_le_one.trans source_haar_base_gt_one.le
  have hpow : sourceHaarBase^4=(3:ℝ) := by
    unfold sourceHaarBase
    rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ)≤3)]
    norm_num
  have hq : sourceHaarBase ≤ (4/3:ℝ) := by
    by_contra hn
    have h4 := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4/3) (le_of_lt (lt_of_not_ge hn)) 4
    rw [hpow] at h4
    norm_num at h4
  have hpi : (3:ℝ) < Real.pi := by linarith [Real.pi_gt_d20]
  have hpi2 : (9:ℝ) ≤ Real.pi^2 := by nlinarith
  have hfac : (23/27:ℝ) ≤ 1-sourceHaarBase/9 := by linarith
  have hd : (23/3:ℝ) ≤ Real.pi^2*(1-sourceHaarBase/9) := by
    have hh := mul_le_mul hpi2 hfac (by norm_num : (0:ℝ)≤23/27) (sq_nonneg Real.pi)
    norm_num at hh
    exact hh
  have hd0 : 0 < Real.pi^2*(1-sourceHaarBase/9) := lt_of_lt_of_le (by norm_num) hd
  have hc0 : 0 ≤ upperCellResetPoincareConstant := div_nonneg hq0 hd0.le
  have hc : upperCellResetPoincareConstant ≤ (4/23:ℝ) := by
    unfold upperCellResetPoincareConstant
    apply (div_le_iff₀ hd0).mpr
    nlinarith only [hq,hd]
  have hs : Real.sqrt 3 ≤ (7/4:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  calc
    _ ≤ (7/4:ℝ)*(4/23)*(156/5) := mul_le_mul_of_nonneg_right
      (mul_le_mul hs hc hc0 (by norm_num)) (by norm_num)
    _ ≤ 10 := by norm_num

end
end ASDExplicitGamma.Scalar
