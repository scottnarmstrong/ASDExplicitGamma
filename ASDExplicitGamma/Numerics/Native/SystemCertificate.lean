module
public import ASDExplicitGamma.Numerics.Native.MatrixReplay

/-! Source-level certificate interface retaining every augmented system and Taylor output. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open Matrix

structure NativeSystemCertificate where
  gap : ℕ
  system : NativeScaledSystem
  result : List ℚ
  initial : ∀ i : Fin 21, 0 ≤ system.v.getD i.val 0 ∧ system.v.getD i.val 0 ≤ 1
  subdiag : ∀ i : Fin 21, 0 ≤ system.subdiag.getD i.val 0 ∧ system.subdiag.getD i.val 0 ≤ 1/2
  force : ∀ i : Fin 21, 0 ≤ system.diag.getD i.val 0 ∧ 0 ≤ system.force.getD i.val 0 ∧ system.force.getD i.val 0 ≤ (1/2 : ℚ)^i.val
  rows : ∀ i : Fin 21, system.subdiag.getD i.val 0+system.diag.getD i.val 0+system.force.getD i.val 0 ≤ 6
  replay : ∀ i : Fin 21, (NormedSpace.exp (nativeSystemMatrix system) *ᵥ nativeVectorReal system.v) i ≤ nativeVectorReal result i

end ASDExplicitGamma.Numerics.Native
