module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B14 : ModeBlockData :=
  ⟨⟨14, 15, (1171174485514684863/156250000000000000000 : ℚ), (353519586525173023/10000000000000000000000 : ℚ)⟩, [
    (14, modeDataJ4M15)], (74955167072939831231/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b14 : entryChecks 4 bflatBlockJ4B14.entries = true := by
  simp only [entryChecks,bflatBlockJ4B14,List.all_cons,List.all_nil,
    mode_checked_j4_m15,Bool.and_self]
theorem block_mass_checked_j4_b14 : blockMassCheck bflatBlockJ4B14 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
