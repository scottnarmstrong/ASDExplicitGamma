module

public import ASDExplicitGamma.Scalar.CrossFam
public import ASDExplicitGamma.Scalar.FlatResolventSourceBridge

/-! The big-cube reference split of the actual NEW quartic: `s₂ = a + s_def` with the flat leg
`a = C r`, `r = σ•inr(FlR z₀) = σ⁻²·uFlat`, and the exact expansion
`q(s₂,s₂) = q(a,a) + 2 q(s_def,a) + q(s_def,s_def)`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

namespace Cfg''

variable (C : Cfg'') (m : ℤ)

/-- The fresh block `C_{z₀}`. -/
def Cz (ω : Cutoff.CutoffSample 2) : C.Pr →L[ℝ] C.Pr :=
  pureFluxBlockOperator 0 (C.Vm (C.z0 m ω))

/-- The reference first response `r = σ·(0, FlR z₀) = σ⁻¹ (0, F)`. -/
def rR (ω : Cutoff.CutoffSample 2) : C.Pr := C.σ • inr'' (Y := C.Ys) (C.FlR (C.z0 m ω))

/-- The flat leg `a = C r`. -/
def aR (ω : Cutoff.CutoffSample 2) : C.Pr := C.Cz m ω (C.rR m ω)

/-- The exact second source `s₂ = C B C u`. -/
def s2R (ω : Cutoff.CutoffSample 2) : C.Pr :=
  C.Cz m ω (C.Bop (C.old m ω) (C.Cz m ω (C.U (C.old m ω))))

theorem s2R_eq (ω : Cutoff.CutoffSample 2) : C.s2R m ω = C.aR m ω + C.sDefR m ω := by
  unfold s2R aR sDefR
  rw [sbil_apply, delta_apply']
  change _ = C.Cz m ω (C.rR m ω) + C.Cz m ω (C.Bop (C.old m ω) (C.Cz m ω (C.U (C.old m ω))) -
    C.rR m ω)
  rw [map_sub]; abel

theorem quartic_expand (ω : Cutoff.CutoffSample 2) :
    ⟪C.Jop (C.s2R m ω), C.Nop m ω (C.s2R m ω)⟫_ℝ =
      ⟪C.Jop (C.aR m ω), C.Nop m ω (C.aR m ω)⟫_ℝ +
        2 * ⟪C.Jop (C.sDefR m ω), C.Nop m ω (C.aR m ω)⟫_ℝ +
        ⟪C.Jop (C.sDefR m ω), C.Nop m ω (C.sDefR m ω)⟫_ℝ := by
  have hsym := JN_symm (Y := C.Ys) (X := C.Xs) C.hα
    (C.Aold (C.old m ω) + C.Vm (C.z0 m ω)) (C.aR m ω) (C.sDefR m ω)
  have hN : ∀ v, C.Nop m ω v = pureFluxBlockInverse C.α C.hα
      (C.Aold (C.old m ω) + C.Vm (C.z0 m ω)) v := fun v => rfl
  rw [s2R_eq]
  simp only [hN, Jop, map_add, inner_add_left, inner_add_right] at hsym ⊢
  linarith

/-- The rotated fixed Wick representative of the flat source (the field `F_flat` of the source). -/
def flatField (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ} (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2)
    (m : ℤ) (ω : Cutoff.CutoffSample 2) : Vec 2 → Vec 2 := fun x =>
  planarQuarterTurn (hilbertVectorL2ToVectorL2 (U := openCubeSet Q)
    (flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω) x)

section Flat

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

theorem aR_toLp (ω : Cutoff.CutoffSample 2) :
    (CC).aR m ω = WithLp.toLp 2 ((CC).Vm ((CC).z0 m ω) ((CC).σ • (CC).FlR ((CC).z0 m ω)),
      (0 : (CC).Xs)) := by
  unfold Cfg''.aR Cfg''.Cz Cfg''.rR
  rw [inr_apply']
  refine WithLp.ofLp_injective 2 ?_
  ext <;> simp [pureFluxBlockOperator_apply]

/-- **The flat leg is the scaled projected rotated Wick field**: `a = σ⁻² (Π F_flat, 0)`. -/
theorem aR_eq (ω : Cutoff.CutoffSample 2) :
    (CC).aR m ω = ((((CC).σ ^ 2)⁻¹ : ℝ)) • (WithLp.toLp 2
      ((physicalFluxSpace (originCube 2 (m + 129))).toSubmodule.subtypeL
        ((physicalFluxSpace (originCube 2 (m + 129))).toSubmodule.orthogonalProjectionOnto
          (toHilbertVectorL2OfVecField
            (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure _
              (flat_source_q3_actual_rotated_wick_admissible
                (originCube 2 (m + 129)) hab hcd hQ e m ω).1))), (0 : (CC).Xs)) : (CC).Pr) := by
  rw [aR_toLp]
  have hins := actual_flat_source_insertion_eq_projected_wick_field
    (originCube 2 (m + 129)) hab hcd hQ M h m ω e
  have hV : (CC).Vm ((CC).z0 m ω) = physicalProjectedInsertion (originCube 2 (m + 129))
      (Annealed.sigmaBar M m) (Annealed.sigmaBar M m).property
      (physicalResponseRestriction (originCube 2 (m + 129))
        (hQcl' hab hcd _ hQ) (shellFieldScalarRestriction (closedRectangle a b c d)
          (ω.1 (m + 1)))) := (CC).Vm_apply _
  let p0 : (CC).Xs := flatSourcePotentialCarrier (originCube 2 (m + 129)) hab hcd e
    (shellFieldScalarRestriction (closedRectangle a b c d) (ω.1 (m + 1)))
  have hFl : (CC).FlR ((CC).z0 m ω) = (((CC).σ ^ 2)⁻¹ : ℝ) • p0 := rfl
  have key : (CC).Vm ((CC).z0 m ω) ((CC).σ • (CC).FlR ((CC).z0 m ω)) =
      (((CC).σ ^ 2)⁻¹ : ℝ) • (CC).Vm ((CC).z0 m ω) ((CC).σ • p0) := by
    rw [hFl, smul_comm, map_smul]
  rw [key, hV]
  erw [hins]
  refine WithLp.ofLp_injective 2 ?_
  ext <;> simp

end Flat

end Cfg''

end

end ASDExplicitGamma.Scalar
