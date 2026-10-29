module

public import ASDExplicitGamma.Inverse.StoppedKuhnSupport

/-! The chosen weak-derivative representative vanishes outside the same
finite closed nodal stars as the literal Kuhn function. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Filter Topology ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

theorem kuhn_nodal_derivative_zero_off_stars (Q : TriadicCube 2) (j : ℕ)
    (b : InteriorNode j → ℝ) {x : Vec 2} (hx : x ∉ nodalClosedStars Q j b) (i : Fin 2) :
    zeroExtendedKuhnAffineCoordDeriv (rootKuhnMesh Q j)
      (diagSynthesisH1Linear Q j b).toFun i x=0 := by
  let line : ℝ → Vec 2 := fun t => i.insertNth t (i.removeNth x)
  have hl : Continuous line := by dsimp only [line]; fun_prop
  have he : line (x i)=x := Fin.insertNth_self_removeNth i x
  have hnot : {y | y ∉ nodalClosedStars Q j b} ∈ 𝓝 (line (x i)) := by
    rw [he]
    exact (nodal_closed_stars_compact Q j b).isClosed.isOpen_compl.mem_nhds hx
  have hn := hl.continuousAt.eventually hnot
  have hz : (fun t => kuhnNodalExtension Q j b (line t)) =ᶠ[𝓝 (x i)] fun _ => (0:ℝ) := by
    filter_upwards [hn] with t ht
    exact kuhn_nodal_extension_zero_off_stars Q j b ht
  change deriv (fun t => kuhnNodalExtension Q j b (line t)) (x i)=0
  rw [hz.deriv_eq]
  exact deriv_const _ _

end
end ASDExplicitGamma.Inverse
