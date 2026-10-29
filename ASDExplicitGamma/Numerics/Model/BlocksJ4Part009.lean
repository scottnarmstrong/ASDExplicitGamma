module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B9 : ModeBlockData :=
  ⟨⟨9, 10, (37673380395944891603/5000000000000000000000 : ℚ), (14187765321147893/400000000000000000000 : ℚ)⟩, [
    (9, modeDataJ4M10)], (15069352158377956641/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b9 : entryChecks 4 bflatBlockJ4B9.entries = true := by
  simp only [entryChecks,bflatBlockJ4B9,List.all_cons,List.all_nil,
    mode_checked_j4_m10,Bool.and_self]
theorem block_mass_checked_j4_b9 : blockMassCheck bflatBlockJ4B9 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
