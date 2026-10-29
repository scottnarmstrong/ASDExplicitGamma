module

public import ASDExplicitGamma.Numerics.Mirror.Composition

/-! Tight signed products for the cancellation-sensitive q3 Fourier moments.
Midpoint/radius products preserve the ordinary interval meaning and are rounded outward.
-/

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
open Mirror

def midpoint (a : QInterval) : ℚ := (a.lo+a.hi)/2
def halfWidth (a : QInterval) : ℚ := (a.hi-a.lo)/2

theorem halfWidth_nonneg (a : QInterval) : 0 ≤ halfWidth a := by
  unfold halfWidth
  exact div_nonneg (sub_nonneg.mpr a.valid) (by norm_num)

theorem contains_midpoint_radius {a : QInterval} {x : ℝ} (h : QInterval.Contains a x) :
    |x-(midpoint a : ℝ)| ≤ (halfWidth a : ℝ) := by
  rw [abs_le]
  change (a.lo : ℝ) ≤ x ∧ x ≤ a.hi at h
  norm_num [midpoint,halfWidth]
  constructor <;> linarith only [h.1,h.2]

def productRadius (a b : QInterval) : ℚ :=
  |midpoint a| *halfWidth b+|midpoint b| *halfWidth a+halfWidth a*halfWidth b

theorem productRadius_nonneg (a b : QInterval) : 0 ≤ productRadius a b := by
  exact add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) (halfWidth_nonneg _))
    (mul_nonneg (abs_nonneg _) (halfWidth_nonneg _)))
    (mul_nonneg (halfWidth_nonneg _) (halfWidth_nonneg _))

def tightMulRaw (a b : QInterval) : QInterval :=
  ⟨midpoint a*midpoint b-productRadius a b,
    midpoint a*midpoint b+productRadius a b, by linarith only [productRadius_nonneg a b]⟩

theorem tightMulRaw_sound {a b : QInterval} {x y : ℝ}
    (hx : QInterval.Contains a x) (hy : QInterval.Contains b y) :
    QInterval.Contains (tightMulRaw a b) (x*y) := by
  have hxa := contains_midpoint_radius hx
  have hyb := contains_midpoint_radius hy
  have hra : (0 : ℝ) ≤ (halfWidth a : ℝ) := by exact_mod_cast halfWidth_nonneg a
  have hrb : (0 : ℝ) ≤ (halfWidth b : ℝ) := by exact_mod_cast halfWidth_nonneg b
  have hprod := mul_le_mul hxa hyb (abs_nonneg _) hra
  have hca := mul_le_mul_of_nonneg_left hyb (abs_nonneg (midpoint a : ℝ))
  have hcb := mul_le_mul_of_nonneg_left hxa (abs_nonneg (midpoint b : ℝ))
  have hsum : |x*y-(midpoint a : ℝ)*(midpoint b : ℝ)| ≤
      |(midpoint a : ℝ)| *|y-(midpoint b : ℝ)|+
      |(midpoint b : ℝ)| *|x-(midpoint a : ℝ)|+
      |x-(midpoint a : ℝ)| *|y-(midpoint b : ℝ)| := by
    calc
      _ = |(midpoint a : ℝ)*(y-(midpoint b : ℝ))+
          (midpoint b : ℝ)*(x-(midpoint a : ℝ))+
          (x-(midpoint a : ℝ))*(y-(midpoint b : ℝ))| := by congr 1; ring
      _ ≤ (|((midpoint a : ℝ)*(y-(midpoint b : ℝ)))|+
          |((midpoint b : ℝ)*(x-(midpoint a : ℝ)))|)+
          |((x-(midpoint a : ℝ))*(y-(midpoint b : ℝ)))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by simp only [abs_mul]
  have he : |x*y-(midpoint a : ℝ)*(midpoint b : ℝ)| ≤ (productRadius a b : ℝ) := by
    norm_num [productRadius]
    linarith only [hsum,hprod,hca,hcb]
  rw [abs_le] at he
  change (((midpoint a*midpoint b-productRadius a b : ℚ) : ℝ) ≤ x*y) ∧
    x*y ≤ ((midpoint a*midpoint b+productRadius a b : ℚ) : ℝ)
  push_cast
  constructor <;> linarith only [he.1,he.2]

def tightMul (G : ℕ) (a b : QInterval) : QInterval := round G (tightMulRaw a b)
theorem tightMul_sound (G : ℕ) {a b : QInterval} {x y : ℝ}
    (hx : QInterval.Contains a x) (hy : QInterval.Contains b y) :
    QInterval.Contains (tightMul G a b) (x*y) := round_contains G (tightMulRaw_sound hx hy)

def tightDiv (G : ℕ) (a b : QInterval) (hb : 0 < b.lo) : QInterval :=
  tightMul G a (QInterval.invPos b hb)
theorem tightDiv_sound (G : ℕ) {a b : QInterval} {x y : ℝ}
    (hx : QInterval.Contains a x) (hb : 0 < b.lo) (hy : QInterval.Contains b y) :
    QInterval.Contains (tightDiv G a b hb) (x/y) := by
  simpa only [tightDiv, div_eq_mul_inv] using tightMul_sound G hx (QInterval.invPos_sound hb hy)

/-- The existing arithmetic trees, with sharp signed products and quotients. -/
def evalTight (G : ℕ) (env : ℕ → QInterval) : Expr → Option QInterval
  | .const q => some (gridConstant G q)
  | .var i => some (env i)
  | .neg e => do return neg G (← evalTight G env e)
  | .add a b => do return add G (← evalTight G env a) (← evalTight G env b)
  | .sub a b => do return sub G (← evalTight G env a) (← evalTight G env b)
  | .mul a b => do return tightMul G (← evalTight G env a) (← evalTight G env b)
  | .divPos a b => do
    let x ← evalTight G env a
    let y ← evalTight G env b
    if h : 0 < y.lo then return tightDiv G x y h else none
  | .sqrt a => do
    let x ← evalTight G env a
    if h : 0 ≤ x.lo then return sqrt G x h else none
  | .exp a => do
    let x ← evalTight G env a
    if hl : -50 ≤ x.lo then
      if hu : x.hi ≤ 50 then return exp G 25 x (by decide) hl hu else none
    else none

theorem evalTight_sound (G : ℕ) (envI : ℕ → QInterval) (envR : ℕ → ℝ)
    (henv : ∀ i, QInterval.Contains (envI i) (envR i)) :
    ∀ e out, evalTight G envI e = some out → QInterval.Contains out (evalReal envR e) := by
  intro e
  induction e with
  | const q =>
    intro out h
    simp only [evalTight, Option.some.injEq] at h
    subst out
    exact gridConstant_sound G q
  | var i =>
    intro out h
    simp only [evalTight, Option.some.injEq] at h
    subst out
    exact henv i
  | neg e ih =>
    intro out h
    cases he : evalTight G envI e with
    | none => simp [evalTight,he] at h
    | some a =>
      simp [evalTight,he] at h
      subst out
      exact neg_sound G (ih a he)
  | add a b ia ib =>
    intro out h
    cases ha : evalTight G envI a with
    | none => simp [evalTight,ha] at h
    | some x =>
      cases hb : evalTight G envI b with
      | none => simp [evalTight,ha,hb] at h
      | some y =>
        simp [evalTight,ha,hb] at h
        subst out
        exact add_sound G (ia x ha) (ib y hb)
  | sub a b ia ib =>
    intro out h
    cases ha : evalTight G envI a with
    | none => simp [evalTight,ha] at h
    | some x =>
      cases hb : evalTight G envI b with
      | none => simp [evalTight,ha,hb] at h
      | some y =>
        simp [evalTight,ha,hb] at h
        subst out
        exact sub_sound G (ia x ha) (ib y hb)
  | mul a b ia ib =>
    intro out h
    cases ha : evalTight G envI a with
    | none => simp [evalTight,ha] at h
    | some x =>
      cases hb : evalTight G envI b with
      | none => simp [evalTight,ha,hb] at h
      | some y =>
        simp [evalTight,ha,hb] at h
        subst out
        exact tightMul_sound G (ia x ha) (ib y hb)
  | divPos a b ia ib =>
    intro out h
    cases ha : evalTight G envI a with
    | none => simp [evalTight,ha] at h
    | some x =>
      cases hb : evalTight G envI b with
      | none => simp [evalTight,ha,hb] at h
      | some y =>
        by_cases hp : 0 < y.lo
        · simp [evalTight,ha,hb,hp] at h
          subst out
          exact tightDiv_sound G (ia x ha) hp (ib y hb)
        · simp [evalTight,ha,hb,hp] at h
  | sqrt a ia =>
    intro out h
    cases ha : evalTight G envI a with
    | none => simp [evalTight,ha] at h
    | some x =>
      by_cases hp : 0 ≤ x.lo
      · simp [evalTight,ha,hp] at h
        subst out
        exact sqrt_sound G hp (ia x ha)
      · simp [evalTight,ha,hp] at h
  | exp a ia =>
    intro out h
    cases ha : evalTight G envI a with
    | none => simp [evalTight,ha] at h
    | some x =>
      by_cases hl : -50 ≤ x.lo
      · by_cases hu : x.hi ≤ 50
        · simp [evalTight,ha,hl,hu] at h
          subst out
          exact exp_sound G 25 (by decide) hl hu (ia x ha)
        · simp [evalTight,ha,hl,hu] at h
      · simp [evalTight,ha,hl] at h

end ASDExplicitGamma.Numerics.Model
