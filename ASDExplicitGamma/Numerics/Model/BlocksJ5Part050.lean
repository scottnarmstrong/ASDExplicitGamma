module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B50 : ModeBlockData :=
  ⟨⟨50, 51, (3114732720105955891/1250000000000000000000 : ℚ), (39213318514227717/10000000000000000000000 : ℚ)⟩, [
    (50, modeDataJ5M51)], (24917861760847647127/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b50 : entryChecks 5 bflatBlockJ5B50.entries = true := by
  simp only [entryChecks,bflatBlockJ5B50,List.all_cons,List.all_nil,
    mode_checked_j5_m51,Bool.and_self]
theorem block_mass_checked_j5_b50 : blockMassCheck bflatBlockJ5B50 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
