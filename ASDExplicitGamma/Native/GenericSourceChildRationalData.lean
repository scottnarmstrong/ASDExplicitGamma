module

public import ASDExplicitGamma.Native.GenericSourceChildAuxNumerics
public import ASDExplicitGamma.Native.CompletedPrefixData

/-! An auxiliary rational refined-mean enclosure, using the stronger direct
old-frame child bank. Its endpoint comparisons retain complete weighted tails. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.Native

/-- Exact shifted-mean coefficient before multiplication by its variance. -/
def nativeSourceChildRationalC : ℚ :=
  2*(65399707/10^9)*nativeB+(259713047/10^9)*nativeB^2

/-- Finite rational endpoint variance at a given source gap. -/
def nativeSourceChildRationalVariance (height : ℕ) : ℚ :=
  (9/2)*nativeGamma*nativeE (2*nativeGamma*height)

/-- The full rare product payment in the auxiliary rational endpoint. -/
def nativeSourceChildRationalRare (high : Bool) (height : ℕ) : ℚ :=
  nativeSourceChildRationalVariance height*
    ((2*(65399707/10^9)+2*nativeB*(259713047/10^9))*
      (4*nativeEps+nativeEps*nativeSourceChildAuxNorm high)+
      (259713047/10^9)*(4*nativeEps^2+nativeEps^2*nativeSourceChildAuxNorm high))

/-- Positive rational child-mean return with the exact carried q1 initial
value and all rare terms. The exponential is enclosed before theta scaling. -/
def nativeSourceChildRationalReturn (high : Bool) (height : ℕ) : ℚ :=
  let e := nativeSourceChildRationalVariance height
  let c := e*nativeSourceChildRationalC
  nativeE (2*nativeGamma*height)*
    (nativeQstar+2*(nativeB+nativeEps)*height*e+
      nativeSourceChildRationalRare high height+4*c)/(1-c)

/-- Every auxiliary rational denominator is positive throughout the refined prefix. -/
theorem native_source_child_rational_domains (height : Fin 161) :
    0 ≤ nativeSourceChildRationalVariance height ∧
    0 ≤ nativeSourceChildRationalC ∧
    nativeSourceChildRationalVariance height*nativeSourceChildRationalC<1 := by
  fin_cases height <;> decide +kernel

/-- Small outward witnesses for the finite refined prefix, at gaps 9 through 64. -/
def nativeSourceChildRationalWitness : Fin 56 → ℚ := ![(5828071/50000000:ℚ),(242531/2000000:ℚ),(2519673/20000000:ℚ),(13071593/100000000:ℚ),(13546237/100000000:ℚ),(7011151/50000000:ℚ),(7249897/50000000:ℚ),(7489359/50000000:ℚ),(15459077/100000000:ℚ),(15940877/100000000:ℚ),(4106031/25000000:ℚ),(16908821/100000000:ℚ),(8697487/50000000:ℚ),(4470647/25000000:ℚ),(18371667/100000000:ℚ),(18862217/100000000:ℚ),(19354243/100000000:ℚ),(79391/400000:ℚ),(20342743/100000000:ℚ),(20839227/100000000:ℚ),(10668603/50000000:ℚ),(21836687/100000000:ℚ),(893507/4000000:ℚ),(11420087/50000000:ℚ),(23344189/100000000:ℚ),(23849727/100000000:ℚ),(24356791/100000000:ℚ),(24865389/100000000:ℚ),(6343881/25000000:ℚ),(25887201/100000000:ℚ),(6600107/25000000:ℚ),(26915207/100000000:ℚ),(13715773/50000000:ℚ),(558989/2000000:ℚ),(28468923/100000000:ℚ),(28989971/100000000:ℚ),(147563/500000:ℚ),(1877301/6250000:ℚ),(30562623/100000000:ℚ),(31090027/100000000:ℚ),(15809517/50000000:ℚ),(32149649/100000000:ℚ),(32681879/100000000:ℚ),(33215727/100000000:ℚ),(33751201/100000000:ℚ),(17144153/50000000:ℚ),(34827047/100000000:ℚ),(35367431/100000000:ℚ),(17954731/50000000:ℚ),(36453147/100000000:ℚ),(9249623/25000000:ℚ),(18772751/50000000:ℚ),(38094183/100000000:ℚ),(38644541/100000000:ℚ),(39196581/100000000:ℚ),(39750311/100000000:ℚ)]

/-- Each finite witness bounds the complete auxiliary rational mean at its gap. -/
theorem native_source_child_rational_witness_bound (i : Fin 56) :
    nativeSourceChildRationalReturn (decide (40<9+i.val)) (9+i.val) ≤
      nativeSourceChildRationalWitness i := by
  fin_cases i <;> decide +kernel

/-- The first six finite means meet the recorded OLD root-source endpoints. -/
theorem native_source_child_rational_mean_bound (r : Fin 6) :
    nativeSourceChildRationalWitness ⟨r.val,by omega⟩ ≤ nativeCompletedPrefixOldMean r := by
  fin_cases r <;> decide +kernel

/-- Auxiliary finite weighted mean sum, retaining all head entries through gap 64. -/
def nativeSourceChildRationalWeightedHead (r : Fin 6) : ℚ :=
  ∑ j : Fin (56-r.val),
    ((759836/1000000:ℚ)^2*nativeE (2*nativeGamma))^j.val*
      nativeSourceChildRationalWitness ⟨r.val+j.val,by omega⟩

/-- The unchanged old weak endpoints cover the stronger refined head,
a positive 10^-5 reserve for the entire remaining mean tail, and a 10^12
whole-trace norm allowance in the rare term. The analytic tail and norm
bounds are separate consumers; this is exact endpoint arithmetic only. -/
theorem native_source_child_rational_weak_bound (r : Fin 6) :
    (1-(759835/1000000:ℚ)^2)*
      (nativeB*(nativeSourceChildRationalWeightedHead r+1/100000)+nativeEps*10^12) ≤
      nativeCompletedPrefixOldXi r := by
  fin_cases r <;> decide +kernel

end ASDExplicitGamma.Native
