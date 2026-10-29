module

public import ASDExplicitGamma.Numerics.Native.Arithmetic

/-! The stable scalar interface for the full VHEAT error term (7). -/

@[expose] public section

namespace ASDExplicitGamma.Native

/-- The generalized-Hölder envelope `J(j,l)` from VHEAT (9). Its consumers
use only `l ≤ p`: below the top degree this is `ε^j X^l`, and at the top
degree it is `ε^j X^p (F/X)^(jp/(128-p))`. -/
noncomputable def nativeHeatVHEATJ (ε X F : ℝ) (p j l : ℕ) : ℝ :=
  if l < p then ε ^ j * X ^ l else
    ε ^ j * X ^ p * Real.rpow (F / X)
      (((j * p : ℕ) : ℝ) / ((128 - p : ℕ) : ℝ))

/-- The exact right-hand side of VHEAT (7), used as the stable `E_k`
interface by the backward heat and remainder-control modules. The second
line of (7) is set to zero for `k < 2`, as in the source. -/
noncomputable def nativeHeatVHEATErrorEk
    (k p : ℕ) (e_h K M S_B θ b X Y ε F : ℝ) : ℝ :=
  let J : ℕ → ℕ → ℝ := nativeHeatVHEATJ ε X F p
  let j1lo := J 1 (k - 1)
  let j1hi := J 1 k
  let j2lo := J 2 (k - 1)
  let j2hi := J 2 k
  let first :=
    (2 * K + 2 * b * M) * (4 * j1lo + j1hi) +
      M * (4 * j2lo + j2hi)
  let bracket :=
    if 2 ≤ k then
      2 * (k : ℝ) * ((k : ℝ) - 1) * e_h * S_B * (1 + θ⁻¹) *
        (b ^ 2 * Y ^ (k - 2) * (4 * X + X ^ 2) +
          2 * b * (4 * j1lo + j1hi) + 4 * j2lo + j2hi)
    else 0
  (k : ℝ) * e_h * first + bracket

end ASDExplicitGamma.Native
