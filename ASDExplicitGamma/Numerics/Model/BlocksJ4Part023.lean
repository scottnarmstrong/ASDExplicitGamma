module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B23 : ModeBlockData :=
  ⟨⟨23, 24, (9233181926427420329/1250000000000000000000 : ℚ), (70048831960634061/2000000000000000000000 : ℚ)⟩, [
    (23, modeDataJ4M24)], (73865455411419362631/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b23 : entryChecks 4 bflatBlockJ4B23.entries = true := by
  simp only [entryChecks,bflatBlockJ4B23,List.all_cons,List.all_nil,
    mode_checked_j4_m24,Bool.and_self]
theorem block_mass_checked_j4_b23 : blockMassCheck bflatBlockJ4B23 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
