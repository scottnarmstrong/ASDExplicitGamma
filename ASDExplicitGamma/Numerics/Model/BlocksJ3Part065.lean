module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B65 : ModeBlockData :=
  ⟨⟨66, 68, (71588841256879427041/10000000000000000000000 : ℚ), (583654337351393047/2500000000000000000000 : ℚ)⟩, [
    (66, modeDataJ3M67),
    (67, modeDataJ3M68)], (71588841256879427039/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b65 : entryChecks 3 bflatBlockJ3B65.entries = true := by
  simp only [entryChecks,bflatBlockJ3B65,List.all_cons,List.all_nil,
    mode_checked_j3_m67,
    mode_checked_j3_m68,Bool.and_self]
theorem block_mass_checked_j3_b65 : blockMassCheck bflatBlockJ3B65 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
