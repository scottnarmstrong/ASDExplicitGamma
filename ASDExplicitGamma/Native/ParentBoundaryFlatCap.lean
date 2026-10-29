module

public import ASDExplicitGamma.Native.ParentRowErrorExpectation
public import ASDExplicitGamma.Native.ParentRowHistoryPanel
public import ASDExplicitGamma.Native.ParentRowOscillationPanel
public import ASDExplicitGamma.Native.ParentRowFlatPayment
public import ASDExplicitGamma.Native.ParentRowEnergyPayment
public import ASDExplicitGamma.Native.ParentRowFlatRootPanel
public import ASDExplicitGamma.Scalar.InverseHistory
public import ASDExplicitGamma.Numerics.Native.PanelFormula

/-! The finite shell sum of the actual flat error cap is paid by its stored
panel fields, preserving the separate oscillation and Dirichlet roots. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Main Triadic Cold Scalar Algsuperdiff.Section3
  ASDExplicitGamma.Numerics.Native
noncomputable section

private theorem sqrt_product_sum {I : Type*} [Fintype I]
    (a b : I → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∑ i, Real.sqrt (a i) * Real.sqrt (b i)) ≤
      Real.sqrt (∑ i, a i) * Real.sqrt (∑ i, b i) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => Real.sqrt (a i)) (fun i => Real.sqrt (b i))
  simpa only [Real.sq_sqrt (ha _), Real.sq_sqrt (hb _)] using h

private theorem sqrt_double_product (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a*b*(a*c)) = a*Real.sqrt b*Real.sqrt c := by
  calc
    Real.sqrt (a*b*(a*c)) = Real.sqrt (a^2*(b*c)) := by congr 1 <;> ring
    _ = Real.sqrt (a^2)*Real.sqrt (b*c) := Real.sqrt_mul (sq_nonneg a) (b*c)
    _ = a*Real.sqrt b*Real.sqrt c := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg ha, Real.sqrt_mul hb]
      ring

/-- The exact finite-shell flat-cap comparison proved separately. -/
theorem parent_row_band_flat_cap
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) (t : ℝ)
    (ht : 0 ≤ t ∧ t ≤ 1)
    (hw : parentRowWeakAllowance (j.val+1) t ≤
      (parentRowFields j).getD 15 0 + (parentRowFields j).getD 12 0*t) :
    let f := fun k => (parentRowFields j).getD k 0
    let X := f 15+f 12*t
    let H := parentRowPanelHistory j t
    let A := 1+2*H+Real.sqrt (2*H)
    (∑ i : Fin (j.val+1), parentRowFlatCap M n (j.val+1) 5 t
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) ≤
      theta M*(Real.sqrt 2*Real.sqrt X*f 8*f 4+
        2*Real.sqrt 2*Real.sqrt ((1+inverseHistoryDiscount)*A*H)*f 9*f 5+
        (3683/2500:ℝ)*(f 4)^2+A*(f 5)^2) := by
  intro f X H A
  let Q := originCube 2 n
  let b := fun i : Fin (j.val+1) =>
    q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ)
  let L := fun i : Fin (j.val+1) => q3ModelLength (n+((i.val+1:ℕ):ℤ))
  let op := fun i : Fin (j.val+1) => descendantsAverage Q 5 (fun U =>
    oldSignedFlatOscillationSize Q U (b i) (L i) true^2)
  let om := fun i : Fin (j.val+1) => descendantsAverage Q 5 (fun U =>
    oldSignedFlatOscillationSize Q U (b i) (L i) false^2)
  let C := parentHistorySourceEnvelope (j.val+1) 5 t
  let A₀ := 1+2*C+Real.sqrt (2*C)
  let D := 1+inverseHistoryDiscount
  let Y := fun i : Fin (j.val+1) => parentBoundaryDirichletEnergy Q (b i) (L i)
  let W := parentRowWeakAllowance (j.val+1) t
  have hC : C=H := by
    dsimp [C]
    exact parent_row_history_panel_eq j t
  have hA : A₀=A := by
    dsimp [A₀,A]
    rw [hC]
  have hθ : 0 < theta M := cold_theta_pos M
  have hθ0 : 0 ≤ theta M := hθ.le
  have hθ1 : theta M ≤ 1 := cold_theta_le_one M hg
  have hθroot1 : Real.sqrt (theta M) ≤ 1 := by
    calc
      Real.sqrt (theta M) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hθ1
      _ = 1 := Real.sqrt_one
  have hweak0 : 0 ≤ W := parent_row_weak_allowance_nonneg (j.val+1) t ht.1
  have hX : 0 ≤ X := hweak0.trans hw
  have hθX : 0 ≤ theta M*X := mul_nonneg hθ0 hX
  have hC0 : 0 ≤ C := by
    rw [hC]
    change 0 ≤ parentRowPanelHistory j t
    unfold parentRowPanelHistory
    exact sq_nonneg _
  have hA0 : 0 ≤ A₀ := by
    dsimp [A₀]
    exact add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hC0))
      (Real.sqrt_nonneg _)
  have hD0 : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have hK0 : 0 ≤ D*A₀*C := mul_nonneg (mul_nonneg hD0 hA0) hC0
  have hf0 : 0 ≤ f 0 := nativeList_getD_nonneg _ (parent_row_fields_valid j).2 0
  have hf4 : 0 ≤ f 4 := nativeList_getD_nonneg _ (parent_row_fields_valid j).2 4
  have hf5 : 0 ≤ f 5 := nativeList_getD_nonneg _ (parent_row_fields_valid j).2 5
  have hf8 : 0 ≤ f 8 := nativeList_getD_nonneg _ (parent_row_fields_valid j).2 8
  have hf9 : 0 ≤ f 9 := nativeList_getD_nonneg _ (parent_row_fields_valid j).2 9
  have hOpRoot : Real.sqrt (∑ i, op i) ≤ Real.sqrt (theta M)*f 4 := by
    simpa [op,Q,f,b,L] using parent_row_band_oscillation_root M h hg n hstate j true
  have hOmRoot : Real.sqrt (∑ i, om i) ≤ Real.sqrt (theta M)*f 5 := by
    simpa [om,Q,f,b,L] using parent_row_band_oscillation_root M h hg n hstate j false
  have hYRoot : Real.sqrt (∑ i, Y i) ≤ Real.sqrt (theta M)*f 9 := by
    simpa [Y,Q,f,b,L,parentBoundaryBandDirichletEnergy] using
      parent_row_actual_dirichlet_root M h hg n hstate j
  have hVar : (∑ i, b i^2) ≤ theta M*f 0 := by
    simpa [b,f,parentBoundaryBandVariance] using
      parent_row_actual_variance M h hg n hstate j
  have hOp0 : ∀ i, 0 ≤ op i := by
    intro i
    exact descendantsAverage_nonneg Q 5 _ (fun U _ => sq_nonneg _)
  have hOm0 : ∀ i, 0 ≤ om i := by
    intro i
    exact descendantsAverage_nonneg Q 5 _ (fun U _ => sq_nonneg _)
  have hY0 : ∀ i, 0 ≤ Y i := by
    intro i
    exact (parent_boundary_dirichlet_energy_bounds Q (b i) (L i)).1
  have hVar0 : 0 ≤ ∑ i, b i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hOpPanel : (∑ i, op i) ≤ theta M*(f 4)^2 := by
    simpa [op,Q,f,b,L] using parent_row_band_oscillation_panel M h hg n hstate j true
  have hOmPanel : (∑ i, om i) ≤ theta M*(f 5)^2 := by
    simpa [om,Q,f,b,L] using parent_row_band_oscillation_panel M h hg n hstate j false
  have hYPanel : (∑ i, Y i) ≤ theta M*(f 9)^2 := by
    have hroot := hYRoot
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2
    have hsum : Real.sqrt (∑ i, Y i)^2 = ∑ i, Y i := by
      rw [Real.sq_sqrt (Finset.sum_nonneg (by intro i hi; exact hY0 i))]
    have hf9root : Real.sqrt (theta M)*(f 9) ≥ 0 :=
      mul_nonneg (Real.sqrt_nonneg _) hf9
    rw [hsum, mul_pow, Real.sq_sqrt hθ0] at hs
    exact hs
  have hweak : W ≤ X := hw
  have hθW : theta M*W ≤ theta M*X := mul_le_mul_of_nonneg_left hweak hθ0
  have hqsum : (∑ i, theta M*W*b i^2) ≤ theta M*X*(theta M*f 0) := by
    calc
      _ = (theta M*W)*(∑ i, b i^2) := by rw [←Finset.mul_sum]
      _ ≤ (theta M*X)*(∑ i, b i^2) := mul_le_mul_of_nonneg_right hθW hVar0
      _ ≤ (theta M*X)*(theta M*f 0) := mul_le_mul_of_nonneg_left hVar hθX
  have hqroot : Real.sqrt (∑ i, theta M*W*b i^2) ≤
      theta M*Real.sqrt X*Real.sqrt (f 0) := by
    calc
      _ ≤ Real.sqrt (theta M*X*(theta M*f 0)) := Real.sqrt_le_sqrt hqsum
      _ = theta M*Real.sqrt X*Real.sqrt (f 0) :=
        sqrt_double_product (theta M) X (f 0) hθ0 hX hf0
  have hplusCS := sqrt_product_sum op (fun i => theta M*W*b i^2) hOp0
    (fun i => mul_nonneg (mul_nonneg hθ0 hweak0) (sq_nonneg _))
  have hplusRoot :
      (∑ i, Real.sqrt (op i)*Real.sqrt (theta M*W*b i^2)) ≤
        (Real.sqrt (theta M)*f 4)*(theta M*Real.sqrt X*Real.sqrt (f 0)) := by
    exact hplusCS.trans (calc
      _ ≤ (Real.sqrt (theta M)*f 4)*Real.sqrt (∑ i, theta M*W*b i^2) :=
        mul_le_mul_of_nonneg_right hOpRoot (Real.sqrt_nonneg _)
      _ ≤ (Real.sqrt (theta M)*f 4)*(theta M*Real.sqrt X*Real.sqrt (f 0)) :=
        mul_le_mul_of_nonneg_left hqroot
          (mul_nonneg (Real.sqrt_nonneg _) hf4))
  have hplusFactor :
      (∑ i, 2*Real.sqrt (op i)*Real.sqrt (theta M*W*b i^2)) =
        2*(∑ i, Real.sqrt (op i)*Real.sqrt (theta M*W*b i^2)) := by
    calc
      _ = ∑ i, 2*(Real.sqrt (op i)*Real.sqrt (theta M*W*b i^2)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [←Finset.mul_sum]
  have hplusSmall :
      2*((Real.sqrt (theta M)*f 4)*(theta M*Real.sqrt X*Real.sqrt (f 0))) ≤
        theta M*(2*Real.sqrt X*Real.sqrt (f 0)*f 4) := by
    calc
      _ = theta M*(Real.sqrt (theta M)*(2*Real.sqrt X*Real.sqrt (f 0)*f 4)) := by ring
      _ ≤ theta M*(1*(2*Real.sqrt X*Real.sqrt (f 0)*f 4)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hθroot1
            (by positivity))
          hθ0
      _ = theta M*(2*Real.sqrt X*Real.sqrt (f 0)*f 4) := by ring
  have h8 : Real.sqrt 2*f 8 = 2*Real.sqrt (f 0) := by
    change Real.sqrt 2*(parentRowFields j).getD 8 0 =
      2*Real.sqrt ((parentRowFields j).getD 0 0)
    rw [parent_row_joint_root_field]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)]
    calc
      _ = (Real.sqrt 2*Real.sqrt 2)*Real.sqrt ((parentRowFields j).getD 0 0) := by ring
      _ = 2*Real.sqrt ((parentRowFields j).getD 0 0) := by
        calc
          _ = (Real.sqrt 2)^2*Real.sqrt ((parentRowFields j).getD 0 0) := by ring
          _ = _ := by rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have hplusCoeff :
      Real.sqrt 2*Real.sqrt X*f 8*f 4=2*Real.sqrt X*Real.sqrt (f 0)*f 4 := by
    calc
      _ = Real.sqrt X*(Real.sqrt 2*f 8)*f 4 := by ring
      _ = _ := by rw [h8]; ring_nf
  have hplus :
      (∑ i, 2*Real.sqrt (op i)*Real.sqrt (theta M*W*b i^2)) ≤
        theta M*(Real.sqrt 2*Real.sqrt X*f 8*f 4) := by
    rw [hplusFactor]
    calc
      _ ≤ 2*((Real.sqrt (theta M)*f 4)*(theta M*Real.sqrt X*Real.sqrt (f 0))) :=
        mul_le_mul_of_nonneg_left hplusRoot (by norm_num)
      _ ≤ theta M*(2*Real.sqrt X*Real.sqrt (f 0)*f 4) := hplusSmall
      _ = theta M*(Real.sqrt 2*Real.sqrt X*f 8*f 4) := by rw [←hplusCoeff]

  have hYrootSquared : (∑ i, Y i) ≤ theta M*(f 9)^2 := hYPanel
  have hzsum : (∑ i, theta M*(D*A₀*C)*Y i) ≤
      theta M*(D*A₀*C)*(theta M*(f 9)^2) := by
    calc
      _ = (theta M*(D*A₀*C))*(∑ i, Y i) := by rw [←Finset.mul_sum]
      _ ≤ (theta M*(D*A₀*C))*(theta M*(f 9)^2) :=
        mul_le_mul_of_nonneg_left hYrootSquared (mul_nonneg hθ0 hK0)
  have hzroot : Real.sqrt (∑ i, theta M*(D*A₀*C)*Y i) ≤
      theta M*Real.sqrt (D*A₀*C)*f 9 := by
    calc
      _ ≤ Real.sqrt (theta M*(D*A₀*C)*(theta M*(f 9)^2)) := Real.sqrt_le_sqrt hzsum
      _ = theta M*Real.sqrt (D*A₀*C)*f 9 := by
        rw [sqrt_double_product (theta M) (D*A₀*C) ((f 9)^2) hθ0 hK0 (sq_nonneg _),
          Real.sqrt_sq_eq_abs, abs_of_nonneg hf9]
  have hminusCS := sqrt_product_sum om (fun i => theta M*(D*A₀*C)*Y i) hOm0
    (fun i => mul_nonneg (mul_nonneg hθ0 hK0) (hY0 i))
  have hminusRoot :
      (∑ i, Real.sqrt (om i)*Real.sqrt (theta M*(D*A₀*C)*Y i)) ≤
        (Real.sqrt (theta M)*f 5)*(theta M*Real.sqrt (D*A₀*C)*f 9) := by
    exact hminusCS.trans (calc
      _ ≤ (Real.sqrt (theta M)*f 5)*Real.sqrt (∑ i, theta M*(D*A₀*C)*Y i) :=
        mul_le_mul_of_nonneg_right hOmRoot (Real.sqrt_nonneg _)
      _ ≤ (Real.sqrt (theta M)*f 5)*(theta M*Real.sqrt (D*A₀*C)*f 9) :=
        mul_le_mul_of_nonneg_left hzroot (mul_nonneg (Real.sqrt_nonneg _) hf5))
  have hminusFactor :
      (∑ i, (2*Real.sqrt 2)*Real.sqrt (om i)*Real.sqrt (theta M*(D*A₀*C)*Y i)) =
        (2*Real.sqrt 2)*(∑ i, Real.sqrt (om i)*Real.sqrt (theta M*(D*A₀*C)*Y i)) := by
    calc
      _ = ∑ i, (2*Real.sqrt 2)*(Real.sqrt (om i)*Real.sqrt (theta M*(D*A₀*C)*Y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [←Finset.mul_sum]
  have hminusSmall :
      (2*Real.sqrt 2)*((Real.sqrt (theta M)*f 5)*(theta M*Real.sqrt (D*A₀*C)*f 9)) ≤
        theta M*(2*Real.sqrt 2*Real.sqrt (D*A₀*C)*f 9*f 5) := by
    calc
      _ = theta M*(Real.sqrt (theta M)*(2*Real.sqrt 2*Real.sqrt (D*A₀*C)*f 9*f 5)) := by ring
      _ ≤ theta M*(1*(2*Real.sqrt 2*Real.sqrt (D*A₀*C)*f 9*f 5)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hθroot1 (by positivity)) hθ0
      _ = theta M*(2*Real.sqrt 2*Real.sqrt (D*A₀*C)*f 9*f 5) := by ring
  have hminusCoeff : Real.sqrt (D*A₀*C)=Real.sqrt (D*A*H) := by rw [hA,hC]
  have hminus :
      (∑ i, (2*Real.sqrt 2)*Real.sqrt (om i)*Real.sqrt (theta M*(D*A₀*C)*Y i)) ≤
        theta M*(2*Real.sqrt 2*Real.sqrt (D*A*H)*f 9*f 5) := by
    rw [hminusFactor]
    calc
      _ ≤ (2*Real.sqrt 2)*((Real.sqrt (theta M)*f 5)*
          (theta M*Real.sqrt (D*A₀*C)*f 9)) :=
        mul_le_mul_of_nonneg_left hminusRoot (by positivity)
      _ ≤ theta M*(2*Real.sqrt 2*Real.sqrt (D*A₀*C)*f 9*f 5) := hminusSmall
      _ = _ := by rw [hminusCoeff]

  have hOpPanel' : (3683/2500:ℝ)*(∑ i, op i) ≤
      theta M*((3683/2500:ℝ)*(f 4)^2) :=
    calc
      _ ≤ (3683/2500:ℝ)*(theta M*(f 4)^2) :=
        mul_le_mul_of_nonneg_left hOpPanel (show (0:ℝ)≤(3683/2500:ℝ) by norm_num)
      _ = _ := by ring
  have hOmPanel' : A₀*(∑ i, om i) ≤ theta M*(A₀*(f 5)^2) :=
    calc
      _ ≤ A₀*(theta M*(f 5)^2) := mul_le_mul_of_nonneg_left hOmPanel hA0
      _ = _ := by ring
  have hsumRewrite :
      (∑ i, (2*Real.sqrt (op i)*Real.sqrt (theta M*W*b i^2) +
        op i*(3683/2500:ℝ) +
        (2*Real.sqrt 2)*Real.sqrt (om i)*Real.sqrt (theta M*(D*A₀*C)*Y i) + A₀*om i)) =
      (∑ i, 2*Real.sqrt (op i)*Real.sqrt (theta M*W*b i^2)) +
        (3683/2500:ℝ)*(∑ i, op i) +
        (∑ i, (2*Real.sqrt 2)*Real.sqrt (om i)*Real.sqrt (theta M*(D*A₀*C)*Y i)) +
        A₀*(∑ i, om i) := by
    simp only [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    ring_nf
  have hmain :
      (∑ i, (2*Real.sqrt (op i)*Real.sqrt (theta M*W*b i^2) +
        op i*(3683/2500:ℝ) +
        (2*Real.sqrt 2)*Real.sqrt (om i)*Real.sqrt (theta M*(D*A₀*C)*Y i) + A₀*om i)) ≤
      theta M*(Real.sqrt 2*Real.sqrt X*f 8*f 4+
        2*Real.sqrt 2*Real.sqrt (D*A*H)*f 9*f 5+
        (3683/2500:ℝ)*(f 4)^2+A*(f 5)^2) := by
    rw [hsumRewrite]
    calc
      _ ≤ theta M*(Real.sqrt 2*Real.sqrt X*f 8*f 4) +
          theta M*((3683/2500:ℝ)*(f 4)^2) +
          theta M*(2*Real.sqrt 2*Real.sqrt (D*A*H)*f 9*f 5) +
          theta M*(A₀*(f 5)^2) :=
        add_le_add (add_le_add (add_le_add hplus hOpPanel') hminus) hOmPanel'
      _ = _ := by rw [←hA]; ring
  simpa only [parentRowFlatCap, Q, b, L, op, om, C, A₀, D, Y, W,
    parent_row_history_panel_eq] using hmain

end
end ASDExplicitGamma.Native
