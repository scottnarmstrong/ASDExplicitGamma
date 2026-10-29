module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B8 : ModeBlockData :=
  ⟨⟨8, 9, (25210984933020402029/10000000000000000000000 : ℚ), (1580230612788979/400000000000000000000 : ℚ)⟩, [
    (8, modeDataJ5M9)], (6302746233255100507/2500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b8 : entryChecks 5 bflatBlockJ5B8.entries = true := by
  simp only [entryChecks,bflatBlockJ5B8,List.all_cons,List.all_nil,
    mode_checked_j5_m9,Bool.and_self]
theorem block_mass_checked_j5_b8 : blockMassCheck bflatBlockJ5B8 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
