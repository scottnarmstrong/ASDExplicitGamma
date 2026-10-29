module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B34 : ModeBlockData :=
  ⟨⟨34, 35, (14377694300921656909/2000000000000000000000 : ℚ), (344275126101644353/10000000000000000000000 : ℚ)⟩, [
    (34, modeDataJ4M35)], (561628683629752223/78125000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b34 : entryChecks 4 bflatBlockJ4B34.entries = true := by
  simp only [entryChecks,bflatBlockJ4B34,List.all_cons,List.all_nil,
    mode_checked_j4_m35,Bool.and_self]
theorem block_mass_checked_j4_b34 : blockMassCheck bflatBlockJ4B34 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
