module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B18 : ModeBlockData :=
  ⟨⟨18, 19, (195143131421784081227/10000000000000000000000 : ℚ), (3438511476921838173/2500000000000000000000 : ℚ)⟩, [
    (18, modeDataJ2M19)], (97571565710892040613/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b18 : entryChecks 2 bflatBlockJ2B18.entries = true := by
  simp only [entryChecks,bflatBlockJ2B18,List.all_cons,List.all_nil,
    mode_checked_j2_m19,Bool.and_self]
theorem block_mass_checked_j2_b18 : blockMassCheck bflatBlockJ2B18 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
