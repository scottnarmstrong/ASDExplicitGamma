module

public import ASDExplicitGamma.Native.ParentRowDerivativeScalar

/-! Physical derivative cap in the homogeneous finite-shell form. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Main Triadic Algsuperdiff.Section3 Numerics.Native
noncomputable section

/-- The actual derivative cap fits the homogeneous form at a larger weak
allowance. The sharp combined derivative multiplier is unchanged. -/
theorem parent_row_derivative_cap_weak_mono
    (M : ABKModel 2) (n : ℤ) (height r : ℕ) (t : ℝ) (ht : 0≤t)
    (b : ℝ) (L : {l : ℝ // 0<l}) (X : ℝ)
    (hw : theta M*parentRowWeakAllowance height t≤X) :
    let Q := originCube 2 n
    let kd := oldSignedDerivativeKappa (cubeScaleFactor Q/3^r) b L.1
    let ka := parentBoundaryPotentialSourceClock Q r b L
    let op := Real.sqrt (descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2))
    let om := Real.sqrt (descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L false^2))
    let Y := parentBoundaryDirichletEnergy Q b L
    let H := parentHistorySourceEnvelope height r t
    let A := 1+2*H+Real.sqrt (2*H)
    parentRowDerivativeCap M n height r t b L≤
      parentRowDerivativeScalarCap (Real.sqrt 2*kd) ka op om b Y X (Real.sqrt ((3683/2500:ℝ)*A)+1) := by
  intro Q kd ka op om Y H A
  let X₀ := theta M*parentRowWeakAllowance height t
  have hX₀ : 0≤X₀ := mul_nonneg (cold_theta_pos M).le (parent_row_weak_allowance_nonneg height t ht)
  have hkd : 0≤kd := old_signed_q1_derivative_kappa_nonneg _ _ _
    (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by positivity))
  have hh := parent_row_derivative_scalar_weak_mono (Real.sqrt 2*kd) ka op om b Y X₀ X
    (Real.sqrt ((3683/2500:ℝ)*A)+1) (mul_nonneg (Real.sqrt_nonneg _) hkd)
    (parent_boundary_potential_source_clock_nonneg Q r b L)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (parent_boundary_dirichlet_energy_bounds Q b L).1
    hX₀ hw (add_nonneg (Real.sqrt_nonneg _) (by norm_num))
  have hN : ((theta M/2)*parentRowWeakAllowance height t)*Y=X₀/2*Y := by
    dsimp only [X₀]
    ring
  change (2*kd*Real.sqrt 2)*(Real.sqrt X₀*Real.sqrt (X₀*b^2)+
    Real.sqrt X₀*Real.sqrt (((theta M/2)*parentRowWeakAllowance height t)*Y)+
    Real.sqrt X₀*Real.sqrt ((Real.sqrt ((3683/2500:ℝ)*A)+1)^2*om^2)+
    ((1+inverseHistoryDiscount)*(op+ka))*((3683/2500:ℝ)*Real.sqrt X₀)+
    ((1+inverseHistoryDiscount)*ka)*((3683/2500:ℝ)*X₀)+
    Real.sqrt (((theta M/2)*parentRowWeakAllowance height t)*Y)+
    Real.sqrt ((Real.sqrt ((3683/2500:ℝ)*A)+1)^2*om^2))≤_
  rw [hN]
  exact (le_of_eq (by ring)).trans hh

/-- Finite-shell derivative contraction against the exact stored physical
root budgets. Only the separately proved weak-field comparison is an
in-node premise; no stochastic moment is assumed. -/
theorem parent_row_band_derivative_cap_contracted
    (M : ABKModel 2) (h : ℝ) (hg : M.gamma≤gammaZero) (n : ℤ)
    (hstate : nativeInductionState M h n) (j : Fin 16) (t : ℝ) (ht : 0≤t ∧ t≤1)
    (hw : parentRowWeakAllowance (j.val+1) t ≤
      (parentRowFields j).getD 15 0+(parentRowFields j).getD 12 0*t) :
    let f := fun k => (parentRowFields j).getD k 0
    let X := f 15+f 12*t
    let H := parentRowPanelHistory j t
    let A := 1+2*H+Real.sqrt (2*H)
    let c := Real.sqrt ((3683/2500:ℝ)*A)+1
    (∑ i : Fin (j.val+1),parentRowDerivativeCap M n (j.val+1) 5 t
      (q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ))
      (q3ModelLength (n+((i.val+1:ℕ):ℤ)))) ≤
      theta M*((2*f 3)*(X*f 8+X*f 9+Real.sqrt X*(c*f 5)+
        ((1+inverseHistoryDiscount)*(f 4+f 2))*((3683/2500:ℝ)*Real.sqrt X)+
        ((1+inverseHistoryDiscount)*f 2)*((3683/2500:ℝ)*X)+Real.sqrt X*f 9+c*f 5)) := by
  intro f X H A c
  let Q := originCube 2 n
  let b := fun i : Fin (j.val+1) => q3ModelAmplitude M h (n+((i.val+1:ℕ):ℤ))/(Annealed.sigmaBar M n:ℝ)
  let L := fun i : Fin (j.val+1) => q3ModelLength (n+((i.val+1:ℕ):ℤ))
  let k := fun i => parentBoundaryPotentialSourceClock Q 5 (b i) (L i)
  let d := fun i => Real.sqrt 2*oldSignedDerivativeKappa (cubeScaleFactor Q/3^5) (b i) (L i).1
  let op := fun i => Real.sqrt (descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U (b i) (L i) true^2))
  let om := fun i => Real.sqrt (descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U (b i) (L i) false^2))
  let y := fun i => parentBoundaryDirichletEnergy Q (b i) (L i)
  have hw0 := parent_row_weak_allowance_nonneg (j.val+1) t ht.1
  have hX : 0≤X := hw0.trans hw
  have hactual : theta M*parentRowWeakAllowance (j.val+1) t≤X :=
    ((mul_le_mul_of_nonneg_right (cold_theta_le_one M hg) hw0).trans_eq (one_mul _)).trans hw
  have hb : Real.sqrt (∑ i,b i^2)≤Real.sqrt (theta M)*f 8 := by
    have hv : 0≤∑ i,b i^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    apply (Real.sqrt_le_sqrt (show (∑ i,b i^2)≤2*(∑ i,b i^2) by linarith only [hv])).trans
    exact parent_row_actual_joint_root M h hg n hstate j
  have hop : Real.sqrt (∑ i,op i^2)≤Real.sqrt (theta M)*f 4 := by
    have he (i) : op i^2=descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U (b i) (L i) true^2) :=
      Real.sq_sqrt (descendantsAverage_nonneg _ _ _ (fun _ _ => sq_nonneg _))
    simp_rw [he]
    exact parent_row_band_oscillation_root M h hg n hstate j true
  have hom : Real.sqrt (∑ i,om i^2)≤Real.sqrt (theta M)*f 5 := by
    have he (i) : om i^2=descendantsAverage Q 5 (fun U => oldSignedFlatOscillationSize Q U (b i) (L i) false^2) :=
      Real.sq_sqrt (descendantsAverage_nonneg _ _ _ (fun _ _ => sq_nonneg _))
    simp_rw [he]
    exact parent_row_band_oscillation_root M h hg n hstate j false
  have hpay := parent_row_derivative_sum_budget d k op om b y (theta M) (f 3) (f 2)
    (f 4) (f 5) (f 8) (f 9) X c (cold_theta_pos M).le
    (nativeList_getD_nonneg _ (parent_row_fields_valid j).2 3) hX
    (add_nonneg (Real.sqrt_nonneg _) (by norm_num))
    (fun i => (parent_boundary_dirichlet_energy_bounds Q (b i) (L i)).1)
    (parent_row_band_derivative_panel M h hg n hstate j)
    (parent_row_band_source_panel M h hg n hstate j) hop hom hb
    (parent_row_actual_dirichlet_root M h hg n hstate j)
  have hi (i) : parentRowDerivativeCap M n (j.val+1) 5 t (b i) (L i)≤
      parentRowDerivativeScalarCap (d i) (k i) (op i) (om i) (b i) (y i) X c := by
    have hh := parent_row_derivative_cap_weak_mono M n (j.val+1) 5 t ht.1 (b i) (L i) X hactual
    dsimp only at hh
    rw [parent_row_history_panel_eq] at hh
    exact hh
  exact (Finset.sum_le_sum (fun i _ => hi i)).trans hpay

end
end ASDExplicitGamma.Native
