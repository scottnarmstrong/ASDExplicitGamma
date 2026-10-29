module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B19 : ModeBlockData :=
  ⟨⟨19, 20, (3720502393012188621/500000000000000000000 : ℚ), (14075294651324561/400000000000000000000 : ℚ)⟩, [
    (19, modeDataJ4M20)], (74410047860243772419/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b19 : entryChecks 4 bflatBlockJ4B19.entries = true := by
  simp only [entryChecks,bflatBlockJ4B19,List.all_cons,List.all_nil,
    mode_checked_j4_m20,Bool.and_self]
theorem block_mass_checked_j4_b19 : blockMassCheck bflatBlockJ4B19 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
