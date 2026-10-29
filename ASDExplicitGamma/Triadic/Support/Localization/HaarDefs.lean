module

-- Ported from GMCExplicitDelta Localization/HaarDefs.lean (Apache-2.0).

public import ASDExplicitGamma.Triadic.Support.Contract.DerivedGeometry
public import ASDExplicitGamma.Triadic.TriadicProjection
public import Homogenization.Ambient.Basic
public import Homogenization.Sobolev.H1.Definitions

/-!
# Localization: vocabulary of the Haar/Neumann analysis (H2–H11)

§8. All objects live on a triadic cube `Q` (in applications `Q_n = originCube d n`, side
`3^n`), with volume-normalized `L²` norms (`Haar.energy`, i.e. `cubeAverage` over the half-open
`cubeSet Q`) and `H¹` functions on the open cube `openCubeSet Q` (CoarseGraining `H1Function`).

* `vecEnergy Q G = ‖G‖² = ∑_i ‖G_i‖²`;
* `vecIncrement Q k G = D_k G`, `vecProjection Q k G = E_k G` (componentwise);
* `IsNeumannPrimitive Q G w`: `w ∈ H¹(Q)` has mean zero and `⨍∇w·∇φ = ⨍G·∇φ` for every `φ ∈ H¹(Q)`
  (the Neumann primitive `w = T G` of H2);
* `multSq row Λ = 𝖻(Λ)² = Λ + (q_s - 1)∑_j q_s^j min{Λ, 9^{-j}η_ω(1 + dΛ)}` (H9); for `k ≥ 1`,
  `multSq row (row.haarL k) = row.haarB k ^ 2`.
-/

@[expose] public section

open Homogenization
open scoped ENNReal

namespace ASDExplicitGamma.Triadic.Support.Localization

open ASDExplicitGamma.Triadic.Support.Contract

variable {d : ℕ}

/-- `w` is the Neumann primitive `T G` of H2: `w ∈ H¹(Q)`, `⨍_Q w = 0`, and `⨍∇w·∇φ = ⨍G·∇φ` for every
`φ ∈ H¹(Q)`. -/
def IsNeumannPrimitive (Q : Homogenization.TriadicCube d)
    (G : Homogenization.Vec d → Homogenization.Vec d) (w : H1Function (openCubeSet Q)) : Prop :=
  cubeAverage Q w.toFun = 0 ∧
    ∀ φ : H1Function (openCubeSet Q),
      cubeAverage Q (fun x => vecDot (w.grad x) (φ.grad x)) =
        cubeAverage Q (fun x => vecDot (G x) (φ.grad x))

end ASDExplicitGamma.Triadic.Support.Localization
