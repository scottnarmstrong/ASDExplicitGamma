module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B29 : ModeBlockData :=
  ⟨⟨29, 30, (6278844435812133967/2500000000000000000000 : ℚ), (19705229612705407/5000000000000000000000 : ℚ)⟩, [
    (29, modeDataJ5M30)], (25115377743248535867/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b29 : entryChecks 5 bflatBlockJ5B29.entries = true := by
  simp only [entryChecks,bflatBlockJ5B29,List.all_cons,List.all_nil,
    mode_checked_j5_m30,Bool.and_self]
theorem block_mass_checked_j5_b29 : blockMassCheck bflatBlockJ5B29 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
