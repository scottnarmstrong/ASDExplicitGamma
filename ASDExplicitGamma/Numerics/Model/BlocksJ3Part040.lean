module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B40 : ModeBlockData :=
  ⟨⟨40, 41, (14891394065808887939/1250000000000000000000 : ℚ), (2160842455286891543/10000000000000000000000 : ℚ)⟩, [
    (40, modeDataJ3M41)], (119131152526471103511/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b40 : entryChecks 3 bflatBlockJ3B40.entries = true := by
  simp only [entryChecks,bflatBlockJ3B40,List.all_cons,List.all_nil,
    mode_checked_j3_m41,Bool.and_self]
theorem block_mass_checked_j3_b40 : blockMassCheck bflatBlockJ3B40 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
