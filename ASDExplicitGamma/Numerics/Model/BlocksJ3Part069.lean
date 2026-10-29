module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B69 : ModeBlockData :=
  ⟨⟨74, 76, (5308392275361351207/1250000000000000000000 : ℚ), (1875906446814476537/10000000000000000000000 : ℚ)⟩, [
    (74, modeDataJ3M75),
    (75, modeDataJ3M76)], (21233569101445404827/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b69 : entryChecks 3 bflatBlockJ3B69.entries = true := by
  simp only [entryChecks,bflatBlockJ3B69,List.all_cons,List.all_nil,
    mode_checked_j3_m75,
    mode_checked_j3_m76,Bool.and_self]
theorem block_mass_checked_j3_b69 : blockMassCheck bflatBlockJ3B69 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
