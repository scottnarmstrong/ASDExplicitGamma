module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B4 : ModeBlockData :=
  ⟨⟨4, 5, (2361956563367526067/312500000000000000000 : ℚ), (355400909607355799/10000000000000000000000 : ℚ)⟩, [
    (4, modeDataJ4M5)], (75582610027760834143/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b4 : entryChecks 4 bflatBlockJ4B4.entries = true := by
  simp only [entryChecks,bflatBlockJ4B4,List.all_cons,List.all_nil,
    mode_checked_j4_m5,Bool.and_self]
theorem block_mass_checked_j4_b4 : blockMassCheck bflatBlockJ4B4 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
