module

public import ASDExplicitGamma.Numerics.Native.PanelFormula

/-! Positive degree comparison for the OLD boundary-fixed panel graph.
Degrees count powers of sqrt(theta); fixed denominators retain their exact
value. The augmented weak parameter has degree zero. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- Twice the gamma degree, together with exact parameter independence. -/
structure NativeBoundaryDegreeTag where
  degree : ℕ
  fixed : Bool
  deriving DecidableEq, Repr

/-- An actual and endpoint value related by the prescribed positive degree. -/
structure NativeBoundaryDegreeControl (z : ℝ) (tag : NativeBoundaryDegreeTag) (x x0 : ℝ) : Prop where
  nonneg : 0 ≤ x
  endpoint_nonneg : 0 ≤ x0
  bound : x ≤ z^tag.degree*x0
  fixed_eq : tag.fixed=true → x=x0

/-- Fixed nonnegative constants have degree zero. -/
theorem native_boundary_degree_const (z : ℝ) (q : ℚ) (hq : 0 ≤ q) :
    NativeBoundaryDegreeControl z ⟨0,true⟩ (q:ℝ) (q:ℝ) := by
  exact ⟨by exact_mod_cast hq,by exact_mod_cast hq,by simp,fun _ => rfl⟩

/-- A higher positive degree can be weakened on the physical theta interval. -/
theorem NativeBoundaryDegreeControl.weaken {z x x0 : ℝ} {tag : NativeBoundaryDegreeTag}
    (h : NativeBoundaryDegreeControl z tag x x0) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (d : ℕ) (hd : d ≤ tag.degree) : x ≤ z^d*x0 :=
  h.bound.trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hz0 hz1 hd) h.endpoint_nonneg)

/-- Positive sums retain the smaller degree. -/
theorem NativeBoundaryDegreeControl.add {z x x0 y y0 : ℝ} {a b : NativeBoundaryDegreeTag}
    (hx : NativeBoundaryDegreeControl z a x x0) (hy : NativeBoundaryDegreeControl z b y y0)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    NativeBoundaryDegreeControl z ⟨min a.degree b.degree,a.fixed && b.fixed⟩ (x+y) (x0+y0) := by
  refine ⟨add_nonneg hx.nonneg hy.nonneg,add_nonneg hx.endpoint_nonneg hy.endpoint_nonneg,?_,?_⟩
  · have hh := add_le_add (hx.weaken hz0 hz1 (min a.degree b.degree) (Nat.min_le_left a.degree b.degree))
      (hy.weaken hz0 hz1 (min a.degree b.degree) (Nat.min_le_right a.degree b.degree))
    simpa only [mul_add] using hh
  · intro h
    rw [Bool.and_eq_true] at h
    have hh := h
    rw [hx.fixed_eq hh.1,hy.fixed_eq hh.2]

/-- Positive products add their degrees. -/
theorem NativeBoundaryDegreeControl.mul {z x x0 y y0 : ℝ} {a b : NativeBoundaryDegreeTag}
    (hx : NativeBoundaryDegreeControl z a x x0) (hy : NativeBoundaryDegreeControl z b y y0)
    (hz0 : 0 ≤ z) :
    NativeBoundaryDegreeControl z ⟨a.degree+b.degree,a.fixed && b.fixed⟩ (x*y) (x0*y0) := by
  refine ⟨mul_nonneg hx.nonneg hy.nonneg,mul_nonneg hx.endpoint_nonneg hy.endpoint_nonneg,?_,?_⟩
  · have hh := mul_le_mul hx.bound hy.bound hy.nonneg
      (mul_nonneg (pow_nonneg hz0 _) hx.endpoint_nonneg)
    convert hh using 1
    rw [pow_add]
    ring
  · intro h
    rw [Bool.and_eq_true] at h
    have hh := h
    rw [hx.fixed_eq hh.1,hy.fixed_eq hh.2]

/-- Division only uses a parameter-independent denominator. No inversion
of a merely endpoint-dominated degree-zero quantity is accepted. -/
theorem NativeBoundaryDegreeControl.div {z x x0 y y0 : ℝ} {a b : NativeBoundaryDegreeTag}
    (hx : NativeBoundaryDegreeControl z a x x0) (hy : NativeBoundaryDegreeControl z b y y0)
    (hb : b.fixed=true) :
    NativeBoundaryDegreeControl z ⟨a.degree,a.fixed && b.fixed⟩ (x/y) (x0/y0) := by
  have he := hy.fixed_eq hb
  refine ⟨div_nonneg hx.nonneg hy.nonneg,div_nonneg hx.endpoint_nonneg hy.endpoint_nonneg,?_,?_⟩
  · rw [he]
    have hh := div_le_div_of_nonneg_right hx.bound hy.endpoint_nonneg
    simpa only [mul_div_assoc] using hh
  · intro h
    rw [Bool.and_eq_true] at h
    have hh := h
    rw [hx.fixed_eq hh.1,he]

/-- Square roots halve an even degree, preserving every positive term. -/
theorem NativeBoundaryDegreeControl.sqrt {z x x0 : ℝ} {a : NativeBoundaryDegreeTag}
    (hx : NativeBoundaryDegreeControl z a x x0) (hz0 : 0 ≤ z) (heven : a.degree%2=0) :
    NativeBoundaryDegreeControl z ⟨a.degree/2,a.fixed⟩ (Real.sqrt x) (Real.sqrt x0) := by
  refine ⟨Real.sqrt_nonneg _,Real.sqrt_nonneg _,?_,?_⟩
  · apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (pow_nonneg hz0 _) (Real.sqrt_nonneg _)
    · have hd : a.degree/2*2=a.degree := by omega
      rw [mul_pow,←pow_mul,hd,Real.sq_sqrt hx.endpoint_nonneg]
      exact hx.bound
  · intro h
    rw [hx.fixed_eq h]

end
end ASDExplicitGamma.Native
