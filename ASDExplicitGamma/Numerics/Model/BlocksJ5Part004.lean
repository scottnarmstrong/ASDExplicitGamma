module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B4 : ModeBlockData :=
  ⟨⟨4, 5, (3152191781421946419/1250000000000000000000 : ℚ), (19756145588358559/5000000000000000000000 : ℚ)⟩, [
    (4, modeDataJ5M5)], (25217534251375571351/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b4 : entryChecks 5 bflatBlockJ5B4.entries = true := by
  simp only [entryChecks,bflatBlockJ5B4,List.all_cons,List.all_nil,
    mode_checked_j5_m5,Bool.and_self]
theorem block_mass_checked_j5_b4 : blockMassCheck bflatBlockJ5B4 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
