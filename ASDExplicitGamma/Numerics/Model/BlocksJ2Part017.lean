module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ2Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ2B17 : ModeBlockData :=
  ⟨⟨17, 18, (223134766608671167943/10000000000000000000000 : ℚ), (3693823178228847123/2500000000000000000000 : ℚ)⟩, [
    (17, modeDataJ2M18)], (111567383304335583971/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j2_b17 : entryChecks 2 bflatBlockJ2B17.entries = true := by
  simp only [entryChecks,bflatBlockJ2B17,List.all_cons,List.all_nil,
    mode_checked_j2_m18,Bool.and_self]
theorem block_mass_checked_j2_b17 : blockMassCheck bflatBlockJ2B17 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
