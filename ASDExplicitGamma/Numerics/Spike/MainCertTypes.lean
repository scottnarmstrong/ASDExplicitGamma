module

public import ASDExplicitGamma.Numerics.CeilDiv

/- Shared structures for generated main-return certificates. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Spike

def gridScale : ℕ := 100000000000000000000000000000000

structure PanelCert where
  aUpper : ℕ
  ellLower : ℕ
  rhoLower : ℕ
  rhoUpper : ℕ
  offsetLower : ℕ
  offsetUpper : ℕ
  supportELower : ℕ
  supportEUpper : ℕ
  supportLambdaLower : ℕ
  supportLambdaUpper : ℕ
  supportJLower : ℕ
  supportJUpper : ℕ
  deriving DecidableEq, Repr

structure InsertionCert where
  observer : ℕ
  frameLower : ℕ
  frameUpper : ℕ
  panels : List PanelCert
  deriving DecidableEq, Repr

def cold40Upper : ℕ := 3426469571810307103625547976069

end ASDExplicitGamma.Numerics.Spike
