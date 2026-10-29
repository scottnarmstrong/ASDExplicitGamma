module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B17 : ModeBlockData :=
  ⟨⟨17, 18, (37323170254265952003/5000000000000000000000 : ℚ), (176296182931704069/5000000000000000000000 : ℚ)⟩, [
    (17, modeDataJ4M18)], (14929268101706380801/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b17 : entryChecks 4 bflatBlockJ4B17.entries = true := by
  simp only [entryChecks,bflatBlockJ4B17,List.all_cons,List.all_nil,
    mode_checked_j4_m18,Bool.and_self]
theorem block_mass_checked_j4_b17 : blockMassCheck bflatBlockJ4B17 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
