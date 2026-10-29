module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B68 : ModeBlockData :=
  ⟨⟨72, 74, (24395064225511156961/5000000000000000000000 : ℚ), (1982656341979305571/10000000000000000000000 : ℚ)⟩, [
    (72, modeDataJ3M73),
    (73, modeDataJ3M74)], (152469151409444731/31250000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b68 : entryChecks 3 bflatBlockJ3B68.entries = true := by
  simp only [entryChecks,bflatBlockJ3B68,List.all_cons,List.all_nil,
    mode_checked_j3_m73,
    mode_checked_j3_m74,Bool.and_self]
theorem block_mass_checked_j3_b68 : blockMassCheck bflatBlockJ3B68 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
