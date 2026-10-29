module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B59 : ModeBlockData :=
  ⟨⟨59, 60, (65057098678229141193/10000000000000000000000 : ℚ), (323366627696802723/10000000000000000000000 : ℚ)⟩, [
    (59, modeDataJ4M60)], (8132137334778642649/1250000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b59 : entryChecks 4 bflatBlockJ4B59.entries = true := by
  simp only [entryChecks,bflatBlockJ4B59,List.all_cons,List.all_nil,
    mode_checked_j4_m60,Bool.and_self]
theorem block_mass_checked_j4_b59 : blockMassCheck bflatBlockJ4B59 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
