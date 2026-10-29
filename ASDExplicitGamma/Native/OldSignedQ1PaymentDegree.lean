module

public import ASDExplicitGamma.Native.BoundaryChargePanelDegree

/-! Positive arithmetic comparison for the complete actual q1 bill.
The weak and history inputs have degree zero; every summand still contains
two powers of the physical amplitude scale. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Mirror
noncomputable section

/-- Physical degrees of variance, amplitude, oscillations, multipliers,
reciprocal and boundary profiles, followed by the panel parameters. -/
def oldSignedQ1PaymentTags : ℕ → NativeBoundaryDegreeTag
  | 0 | 2 | 3 | 6 | 7 | 14 => ⟨2,false⟩
  | 1 | 4 | 5 | 15 => ⟨1,false⟩
  | 10 | 11 | 12 => ⟨0,true⟩
  | _ => ⟨0,false⟩

def oldSignedQ1AffineExpr : Expr :=
  (.add (.add (.mul (.divPos (.var 0) (.const 2)) (.var 13)) (.mul (.mul (.const 2) (.var 0)) (.const (1183/2500)))) (.divPos (.mul (.mul (.add (.const 4) (.mul (.const 2) (.sqrt (.const 2)))) (.const (156/5))) (.var 14)) (.const 9)))

def oldSignedQ1FlatExpr : Expr :=
  (.add (.add (.add (.mul (.mul (.const 2) (.sqrt (.var 2))) (.sqrt (.mul (.var 8) (.var 0)))) (.mul (.const (3683/2500)) (.var 2))) (.mul (.mul (.mul (.const 2) (.sqrt (.const 2))) (.sqrt (.var 3))) (.sqrt (.mul (.var 9) (.var 0))))) (.mul (.var 10) (.var 3)))

def oldSignedQ1SourceExpr : Expr :=
  (.add (.add (.mul (.mul (.mul (.var 4) (.var 4)) (.const (3683/2500))) (.var 8)) (.mul (.mul (.mul (.const 2) (.var 4)) (.var 8)) (.var 1))) (.mul (.mul (.mul (.const 2) (.var 4)) (.sqrt (.var 8))) (.sqrt (.var 6))))

def oldSignedQ1DerivativeExpr : Expr :=
  (.add (.mul (.mul (.mul (.const 2) (.var 5)) (.sqrt (.const 2))) (.add (.add (.add (.add (.add (.mul (.var 8) (.var 1)) (.mul (.sqrt (.var 8)) (.sqrt (.divPos (.mul (.var 8) (.var 0)) (.const 2))))) (.mul (.mul (.sqrt (.var 8)) (.var 12)) (.sqrt (.var 3)))) (.mul (.mul (.mul (.var 11) (.add (.sqrt (.var 2)) (.var 4))) (.const (3683/2500))) (.sqrt (.var 8)))) (.sqrt (.divPos (.mul (.var 8) (.var 0)) (.const 2)))) (.mul (.var 12) (.sqrt (.var 3))))) (.mul (.mul (.mul (.mul (.mul (.const 2) (.var 15)) (.var 11)) (.var 4)) (.const (3683/2500))) (.var 8)))

def oldSignedQ1BoundaryExpr : Expr :=
  (.mul (.mul (.const 2) (.var 7)) (.add (.sqrt (.var 8)) (.sqrt (.mul (.const 2) (.var 8)))))

/-- The four positive AN error blocks together with the affine payment. -/
def oldSignedQ1PaymentExpr : Expr :=
  .add oldSignedQ1AffineExpr (.add (.add (.add oldSignedQ1FlatExpr
    oldSignedQ1SourceExpr) oldSignedQ1DerivativeExpr) oldSignedQ1BoundaryExpr)

/-- Kernel-checked homogeneity of the complete bill. -/
theorem old_signed_q1_payment_degree_checked :
    nativeBoundaryExprDegree oldSignedQ1PaymentTags oldSignedQ1PaymentExpr=some ⟨2,false⟩ := by
  decide +kernel

/-- The complete positive bill retains one full theta factor. -/
theorem old_signed_q1_payment_degree_bound (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (values endpoint : ℕ → ℝ)
    (hv : ∀ i, NativeBoundaryDegreeControl (Real.sqrt θ) (oldSignedQ1PaymentTags i)
      (values i) (endpoint i)) :
    evalReal values oldSignedQ1PaymentExpr ≤ θ*evalReal endpoint oldSignedQ1PaymentExpr := by
  have hh := (native_boundary_expr_degree_sound (Real.sqrt θ) (Real.sqrt_nonneg θ)
    (Real.sqrt_le_one.mpr hθ1) oldSignedQ1PaymentTags values endpoint hv
    oldSignedQ1PaymentExpr ⟨2,false⟩ old_signed_q1_payment_degree_checked).bound
  simpa only [Real.sq_sqrt hθ0] using hh

end
end ASDExplicitGamma.Native
