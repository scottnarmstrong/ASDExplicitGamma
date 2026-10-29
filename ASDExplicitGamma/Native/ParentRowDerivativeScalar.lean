module

public import ASDExplicitGamma.Native.ParentRowSourceCapComparison

/-! Homogeneous derivative scalar cap for the complete shell contraction. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Main Triadic Algsuperdiff.Section3
noncomputable section

/-- The homogeneous derivative bill uses the sharp combined multiplier d;
its actual specialization is d=sqrt(2)*kd. -/
def parentRowDerivativeScalarCap (d k op om b y X c : ℝ) : ℝ :=
  let D := 1+inverseHistoryDiscount
  (2*d)*(X*|b|+X*Real.sqrt y+Real.sqrt X*(c*om)+
    (D*(op+k))*((3683/2500:ℝ)*Real.sqrt X)+
    (D*k)*((3683/2500:ℝ)*X)+Real.sqrt X*Real.sqrt y+c*om)

/-- Monotonic weak replacement in the derivative bill, retaining the exact
Dirichlet energy while using its full rather than half allowance. -/
theorem parent_row_derivative_scalar_weak_mono
    (d k op om b y X₀ X c : ℝ)
    (hd : 0≤d) (hk : 0≤k) (hop : 0≤op) (hom : 0≤om) (hy : 0≤y)
    (hX₀ : 0≤X₀) (hX : X₀≤X) (hc : 0≤c) :
    (2*d)*(Real.sqrt X₀*Real.sqrt (X₀*b^2)+Real.sqrt X₀*Real.sqrt (X₀/2*y)+
      Real.sqrt X₀*Real.sqrt (c^2*om^2)+
      ((1+inverseHistoryDiscount)*(op+k))*((3683/2500:ℝ)*Real.sqrt X₀)+
      ((1+inverseHistoryDiscount)*k)*((3683/2500:ℝ)*X₀)+Real.sqrt (X₀/2*y)+Real.sqrt (c^2*om^2))≤
      parentRowDerivativeScalarCap d k op om b y X c := by
  have hXpos := hX₀.trans hX
  have hD : 0≤1+inverseHistoryDiscount := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have hn : X₀/2*y≤X*y := mul_le_mul_of_nonneg_right ((half_le_self hX₀).trans hX) hy
  have hnr : Real.sqrt (X₀/2*y)≤Real.sqrt X*Real.sqrt y := by
    rw [←Real.sqrt_mul hXpos]
    exact Real.sqrt_le_sqrt hn
  have hnm : Real.sqrt X₀*Real.sqrt (X₀/2*y)≤X*Real.sqrt y := by
    have hh := mul_le_mul (Real.sqrt_le_sqrt hX) hnr (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg X)
    exact hh.trans_eq (by rw [←mul_assoc,←pow_two,Real.sq_sqrt hXpos])
  have hoff : Real.sqrt (c^2*om^2)=c*om := by
    rw [Real.sqrt_mul (sq_nonneg c),Real.sqrt_sq hc,Real.sqrt_sq hom]
  rw [hoff,parent_row_weak_variance_root X₀ b hX₀]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hd)
  exact add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right hX (abs_nonneg b)) hnm)
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hX) (mul_nonneg hc hom)))
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hX)
      (by norm_num : (0:ℝ)≤3683/2500)) (mul_nonneg hD (add_nonneg hop hk))))
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX
      (by norm_num : (0:ℝ)≤3683/2500)) (mul_nonneg hD hk))) hnr) le_rfl

/-- All derivative cross products share the same Euclidean multiplier
budget. In particular its quadratic source term keeps the sqrt(2) gain. -/
theorem parent_row_derivative_sum_budget {I : Type*} [Fintype I]
    (d k op om b y : I → ℝ) (θ Dk K Op Om V Y X c : ℝ)
    (hθ : 0≤θ) (hDk : 0≤Dk) (hX : 0≤X) (hc : 0≤c) (hy : ∀ i,0≤y i)
    (hd : Real.sqrt (∑ i,d i^2)≤Real.sqrt θ*Dk)
    (hk : Real.sqrt (∑ i,k i^2)≤Real.sqrt θ*K)
    (hop : Real.sqrt (∑ i,op i^2)≤Real.sqrt θ*Op)
    (hom : Real.sqrt (∑ i,om i^2)≤Real.sqrt θ*Om)
    (hb : Real.sqrt (∑ i,b i^2)≤Real.sqrt θ*V)
    (hyr : Real.sqrt (∑ i,y i)≤Real.sqrt θ*Y) :
    (∑ i,parentRowDerivativeScalarCap (d i) (k i) (op i) (om i) (b i) (y i) X c)≤
      θ*((2*Dk)*(X*V+X*Y+Real.sqrt X*(c*Om)+
        ((1+inverseHistoryDiscount)*(Op+K))*((3683/2500:ℝ)*Real.sqrt X)+
        ((1+inverseHistoryDiscount)*K)*((3683/2500:ℝ)*X)+Real.sqrt X*Y+c*Om)) := by
  let D := 1+inverseHistoryDiscount
  let B := (3683/2500:ℝ)
  have hD : 0≤D := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have hB : 0≤B := by norm_num [B]
  have hdb := parent_row_pair_budget d (fun i => |b i|) θ Dk V hθ hDk hd
    (by simpa only [sq_abs] using hb)
  have hdy := parent_row_pair_budget d (fun i => Real.sqrt (y i)) θ Dk Y hθ hDk hd
    (by simpa only [Real.sq_sqrt (hy _)] using hyr)
  have hdo := parent_row_pair_budget d op θ Dk Op hθ hDk hd hop
  have hdm := parent_row_pair_budget d om θ Dk Om hθ hDk hd hom
  have hdk := parent_row_pair_budget d k θ Dk K hθ hDk hd hk
  have he : (∑ i,parentRowDerivativeScalarCap (d i) (k i) (op i) (om i) (b i) (y i) X c)=
      2*(X*(∑ i,d i*|b i|)+X*(∑ i,d i*Real.sqrt (y i))+
        (Real.sqrt X*c)*(∑ i,d i*om i)+(D*B*Real.sqrt X)*((∑ i,d i*op i)+(∑ i,d i*k i))+
        (D*B*X)*(∑ i,d i*k i)+Real.sqrt X*(∑ i,d i*Real.sqrt (y i))+c*(∑ i,d i*om i)) := by
    simp only [Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [parentRowDerivativeScalarCap,D,B]
    ring
  rw [he]
  have hh := add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hdb hX) (mul_le_mul_of_nonneg_left hdy hX))
    (mul_le_mul_of_nonneg_left hdm (mul_nonneg (Real.sqrt_nonneg X) hc)))
    (mul_le_mul_of_nonneg_left (add_le_add hdo hdk) (mul_nonneg (mul_nonneg hD hB) (Real.sqrt_nonneg X))))
    (mul_le_mul_of_nonneg_left hdk (mul_nonneg (mul_nonneg hD hB) hX)))
    (mul_le_mul_of_nonneg_left hdy (Real.sqrt_nonneg X))) (mul_le_mul_of_nonneg_left hdm hc)
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤2)).trans_eq
    (by dsimp only [D,B]; ring)

end
end ASDExplicitGamma.Native
