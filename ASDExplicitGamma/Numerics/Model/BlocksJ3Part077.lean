module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B77 : ModeBlockData :=
  ⟨⟨90, 92, (2216737883922267887/2000000000000000000000 : ℚ), (18852852294661379/156250000000000000000 : ℚ)⟩, [
    (90, modeDataJ3M91),
    (91, modeDataJ3M92)], (11083689419611339433/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b77 : entryChecks 3 bflatBlockJ3B77.entries = true := by
  simp only [entryChecks,bflatBlockJ3B77,List.all_cons,List.all_nil,
    mode_checked_j3_m91,
    mode_checked_j3_m92,Bool.and_self]
theorem block_mass_checked_j3_b77 : blockMassCheck bflatBlockJ3B77 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
