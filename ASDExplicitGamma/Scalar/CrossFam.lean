module

public import ASDExplicitGamma.Scalar.PureCross
public import ASDExplicitGamma.Scalar.RefFamFinal

/-! Wick-truncation cross term for an arbitrary pure first-source family `a(ω)`: pathwise bound on the
truncations `⟪J s_n, N a⟫`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

namespace Cfg''

variable (C : Cfg'') (m : ℤ)

theorem cross_trunc_le (M : ABKModel 2) (hν : C.ν = M.nu)
    (hσ' : C.σ = (Annealed.sigmaBar M m : ℝ))
    (ell : ℤ) (hK : C.K ⊆ openCubeSet (originCube 2 ell))
    (ω : Cutoff.CutoffSample 2) (n : ℕ) (x : Fin n → ℝ)
    {Fa : Vec 2 → Vec 2} (hFa : MemVectorL2 (openCubeSet C.Q) Fa)
    (hFac : ∀ U ∈ descendantsAtDepth C.Q 134, MemLp Fa 2 (normalizedCubeMeasure U) ∧
      ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3) ^ (j + 1) *
        energy U (cubeIncrement U (j + 1) (fun x => Fa x i))))
    (s₁ : C.Ys) (hs1 : s₁ ∈ (physicalFluxSpace C.Q).toSubmodule)
    (hs1' : ∀ w ∈ (physicalFluxSpace C.Q).toSubmodule,
      ⟪s₁, w⟫_ℝ = ⟪toHilbertVectorL2OfVecField hFa, w⟫_ℝ)
    (a : C.Pr) (ha : a = WithLp.toLp 2 (s₁, (0 : C.Xs))) :
    ⟪C.Jop (C.sTruncR m ω n x), C.Nop m ω a⟫_ℝ ≤ (141 / 100 : ℝ) *
      ((volume (openCubeSet C.Q)).toReal *
        (Real.sqrt (bnew M m C.Q ω * lemmaVTiledPositiveEnergy C.Q 134 Fa) *
          Real.sqrt (bnew M m C.Q ω *
            (tiledPositiveEnergy C.Q 134 (psdDefectSource (C.BFoR (C.old m ω) n) x) +
             tiledPositiveEnergy C.Q 134 (psdDefectSource (C.BGoR (C.old m ω) n) x))))) := by
  have hsn := C.sn_identR (C.old m ω) n x
  have hF := C.BFoR_memL2 (C.old m ω) n x
  have hG := C.BGoR_memL2 (C.old m ω) n x
  have hB := Bnew_cell_bound M ell m C.Q ω C.K C.hQcl hK
  rw [← hν, ← hσ'] at hB
  have hFc := tiled_vec_admissible C.Q 134 (psdDefectSource (C.BFoR (C.old m ω) n) x)
  have hGc := tiled_vec_admissible C.Q 134 (psdDefectSource (C.BGoR (C.old m ω) n) x)
  have main := pure_cross_bound C.Q 134 C.hν C.hσ
    (C.Rest (modelInsertedScalar C.K m 1 ω)) hFa hF hG hFac hFc hGc s₁ hs1 hs1'
    (fluxSource C.Q hF) (potSource C.Q hG) (fluxSource_inner C.Q hF)
    (potSource_inner C.Q hG) hB
  unfold sTruncR
  rw [hsn, Nop_eq, ha]
  exact main

end Cfg''

end

end ASDExplicitGamma.Scalar
