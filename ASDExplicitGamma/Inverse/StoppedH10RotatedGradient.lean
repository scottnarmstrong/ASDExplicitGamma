module

public import ASDExplicitGamma.Variational.AdapterConstantSkew
public import Homogenization.Sobolev.MatchedPair.Core

/-! A chosen H1 zero-trace representative has an admissible rotated gradient.
Gradient uniqueness discharges the H10 witness representative internally. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Response
noncomputable section

theorem rotated_h10_gradient_admissible {U : Set (Vec 2)} (hU : IsOpen U)
    (u : H1Function U) (hu : MemH10 U u.toFun) :
    MemVectorL2 U (fun x => matVecMul responsePlanarJ (u.grad x)) ∧
      IsSolenoidalZeroNormalTraceOn U (fun x => matVecMul responsePlanarJ (u.grad x)) := by
  constructor
  · apply MemLp.of_eval
    intro i
    fin_cases i
    · have hh := (u.gradMemL2 1).neg
      change MemLp (fun x => -u.grad x 1) 2 (volumeMeasureOn U) at hh
      simpa [matVecMul,responsePlanarJ,Fin.sum_univ_two] using hh
    · simpa [matVecMul,responsePlanarJ,Fin.sum_univ_two] using u.gradMemL2 0
  · obtain ⟨v,hv⟩ := hu
    have he (i : Fin 2) := gradCoord_ae_eq_of_toFun_eq hU v.toH1Function u hv i
    have hae : v.toH1Function.grad =ᵐ[volume.restrict U] u.grad := by
      filter_upwards [ae_all_iff.mpr he] with x hx
      exact funext hx
    have hs := ASDExplicitGamma.Variational.planarJ_gradient_isSolenoidalZeroNormalTrace v
    intro w
    calc
      (∫ x in U, vecDot (matVecMul responsePlanarJ (u.grad x)) (w.grad x))=
          ∫ x in U, vecDot (matVecMul responsePlanarJ (v.toH1Function.grad x)) (w.grad x) := by
        apply integral_congr_ae
        filter_upwards [hae] with x hx
        rw [hx]
      _ = 0 := hs w

end
end ASDExplicitGamma.Inverse
