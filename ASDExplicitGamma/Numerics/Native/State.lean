module
public import ASDExplicitGamma.Numerics.Native.Arithmetic

/-! The actual native raw and four-step old envelopes, and the individual-system coefficients.
These are the formulas of the configured individual branch.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

def nativeE (x : ℚ) : ℚ := 1/(1-(11/10)*x)
def nativeB : ℚ := 3683/2500
def nativeEps : ℚ := 3/10^46

def nativeRaw (h : ℕ) : ℚ × ℚ × ℚ :=
  let e := (9/2)*nativeGamma*nativeE (2*nativeGamma*h)
  let f := nativeUp (4*((1009309/500000)+nativeGamma*(32474*(h+1)+11483216))*
    nativeE ((2*h+4)*nativeGamma))
  let hc := nativeUp (e*(((4*20-2)*h+4*19*(521/1000))*nativeB+
    2*(521/1000)*nativeB*f+((1975/1000)+2*19*(1565/1000))*nativeB^2*f))
  (f,e,hc)

def nativeOldStep (h : ℕ) (f e hc : ℚ) : ℚ :=
  let x := (7/2)*nativeA+hc
  let u1 := min f (4+x*nativeRootUp ((f/x)^5) 27)
  let u2 := min f (4+x*nativeRootUp ((f/x)^10) 27)
  let d := min (2*nativeB) (2+x+nativeRootUp (2*x))
  let hn := nativeUp (e*(((2*20-1)*h+2*19*(521/1000))*d+
    2*(521/1000)*nativeB*u1+((1975/1000)+2*19*(1565/1000))*nativeB^2*u2))
  min hc hn

structure NativeOldRow where
  x : ℚ
  y : ℚ
  f : ℚ
  e : ℚ
  hc : ℚ
  deriving DecidableEq

def nativeOldFrom (h : ℕ) (f e hc : ℚ) : NativeOldRow :=
  let hc := nativeOldStep h f e hc
  let hc := nativeOldStep h f e hc
  let hc := nativeOldStep h f e hc
  let hc := nativeOldStep h f e hc
  ⟨nativeUp ((7/2)*nativeA+hc), nativeUp (nativeAvg*nativeA+hc), f, e, hc⟩

def nativeOld (h : ℕ) : NativeOldRow :=
  let (f,e,hc) := nativeRaw h
  nativeOldFrom h f e hc

structure NativeSystemCoefficients where
  alpha : List ℚ
  beta : List ℚ
  force : List ℚ
  deriving DecidableEq

def nativeRareJ (x f : ℚ) (j l : ℕ) : ℚ :=
  nativeUp (nativeEps^j*x^l*(if l=20 then nativeRootUp ((f/x)^(5*j)) 27 else 1))

def nativeIndividualRow (h k : ℕ) (old : NativeOldRow) : ℚ × ℚ × ℚ :=
  let c : ℚ := (1975/1000)+2*((k-1 : ℕ) : ℚ)*(1565/1000)
  let d := 2*(h : ℚ)+4*(k-1)*((h : ℚ)+(521/1000))
  let al := nativeUp ((k : ℚ)*old.e*(d*nativeB+4*(2*(521/1000)*nativeB+c*nativeB^2))/nativeA)
  let be := nativeUp ((k : ℚ)*old.e*(2*(521/1000)*nativeB+c*nativeB^2))
  let j1prev := nativeRareJ old.x old.f 1 (k-1)
  let j1 := nativeRareJ old.x old.f 1 k
  let j2prev := nativeRareJ old.x old.f 2 (k-1)
  let j2 := nativeRareJ old.x old.f 2 k
  let er := (k : ℚ)*old.e*(d*j1prev+(2*(521/1000)+2*nativeB*c)*(4*j1prev+j1)+c*(4*j2prev+j2))
  (al,be,nativeUp (er/nativeA^k))

def nativeIndividualCoefficients (h : ℕ) (old : NativeOldRow) : NativeSystemCoefficients :=
  let rows := (List.range 20).map fun j => nativeIndividualRow h (j+1) old
  ⟨rows.map Prod.fst, rows.map (Prod.fst ∘ Prod.snd), rows.map (Prod.snd ∘ Prod.snd)⟩

structure NativeScaledSystem where
  z : ℚ
  v : List ℚ
  subdiag : List ℚ
  diag : List ℚ
  force : List ℚ
  deriving DecidableEq

def nativeScaledFrom (coeff : NativeSystemCoefficients) (rr z : ℚ) : NativeScaledSystem :=
  ⟨z,1 :: ((List.range 20).map fun j => nativeUp (rr^j/z^(j+1))),
    0 :: coeff.alpha.map (fun a => a/z), 0 :: coeff.beta,
    0 :: ((List.range 20).map fun j => coeff.force.getD j 0/z^(j+1))⟩

/-- Sparse augmented multiplication; row zero is zero and forcing is in column zero. -/
def nativeMatVec (s : NativeScaledSystem) (v : List ℚ) : List ℚ :=
  0 :: ((List.range 20).map fun j =>
    nativeUp (s.diag.getD (j+1) 0*v.getD (j+1) 0+
      s.subdiag.getD (j+1) 0*v.getD j 0+s.force.getD (j+1) 0*v.getD 0 0))

/-- Taylor steps retain both the current term and the accumulated sum. -/
def nativeTaylorSteps (s : NativeScaledSystem) : ℕ → ℕ → List ℚ → List ℚ → List ℚ × List ℚ
  | 0, _, term, accum => (term,accum)
  | fuel+1, n, term, accum =>
    let term' := (nativeMatVec s term).map fun x => nativeUp (x/(n+1 : ℕ))
    let accum' := List.zipWith (·+·) accum term'
    nativeTaylorSteps s fuel (n+1) term' accum'

def nativeExpTail : ℚ := (6^161/(Nat.factorial 161))/(1-6/162)

def nativeTaylorFinal (accum : List ℚ) : List ℚ :=
  accum.getD 0 0 :: ((accum.drop 1).map fun x => nativeUp (x+nativeExpTail))

end ASDExplicitGamma.Numerics.Native
