module

public import ASDExplicitGamma.Inverse.StoppedLocalRegionSeparation
public import Mathlib.Data.Int.ModEq
public import Mathlib.Algebra.Order.Ring.Abs

/-! The literal (7N)^2 residue colors separate complete localized observation fields. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- The source two-coordinate residue palette, N=3^M. -/
abbrev LocalizationColor (M : ℕ) := Fin 2 → Fin (7*3^M)

/-- Literal residues of possibly negative block coordinates. -/
def localizationColor (M : ℕ) (x : BlockSite) : LocalizationColor M := fun d =>
  ⟨(x d%((7*3^M:ℕ):ℤ)).toNat,by
    have hpos : (0:ℤ) < ((7*3^M:ℕ):ℤ) := by positivity
    have h0 := Int.emod_nonneg (x d) hpos.ne'
    have h1 := Int.emod_lt_of_pos (x d) hpos
    omega⟩

theorem localization_color_card (M : ℕ) : Fintype.card (LocalizationColor M) = (7*3^M)^2 := by
  simp only [LocalizationColor,Fintype.card_fun,Fintype.card_fin]

/-- Distinct sites of one source color have a coordinate gap at least 7N. -/
theorem localization_color_separation (M : ℕ) (x y : BlockSite) (hne : x ≠ y)
    (hc : localizationColor M x = localizationColor M y) :
    ∃ d, (7:ℤ)*(3^M:ℤ) ≤ |y d-x d| := by
  have hex : ∃ d, x d ≠ y d := by
    by_contra! he
    exact hne (funext he)
  obtain ⟨d,hd⟩ := hex
  have hc' := congrArg Fin.val (congrFun hc d)
  change (x d%((7*3^M:ℕ):ℤ)).toNat = (y d%((7*3^M:ℕ):ℤ)).toNat at hc'
  have hpos : (0:ℤ) < ((7*3^M:ℕ):ℤ) := by positivity
  have h0 := Int.emod_nonneg (x d) hpos.ne'
  have h1 := Int.emod_nonneg (y d) hpos.ne'
  have hmod : x d%((7*3^M:ℕ):ℤ) = y d%((7*3^M:ℕ):ℤ) := by omega
  have hme : Int.ModEq ((7*3^M:ℕ):ℤ) (x d) (y d) := hmod
  have hh := Int.le_abs_of_dvd (sub_ne_zero.mpr hd.symm) hme.dvd
  refine ⟨d,?_⟩
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using! hh

end ASDExplicitGamma.Inverse
