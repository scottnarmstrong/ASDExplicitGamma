module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part001

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B31 : ModeBlockData :=
  ⟨⟨31, 32, (9061943527645168001/1250000000000000000000 : ℚ), (69222353285288353/2000000000000000000000 : ℚ)⟩, [
    (31, modeDataJ4M32)], (72495548221161344007/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b31 : entryChecks 4 bflatBlockJ4B31.entries = true := by
  simp only [entryChecks,bflatBlockJ4B31,List.all_cons,List.all_nil,
    mode_checked_j4_m32,Bool.and_self]
theorem block_mass_checked_j4_b31 : blockMassCheck bflatBlockJ4B31 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
