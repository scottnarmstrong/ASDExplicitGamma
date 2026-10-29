module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part000

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B6 : ModeBlockData :=
  ⟨⟨6, 7, (37753532627370577733/5000000000000000000000 : ℚ), (88793643412607671/2500000000000000000000 : ℚ)⟩, [
    (6, modeDataJ4M7)], (15101413050948231093/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b6 : entryChecks 4 bflatBlockJ4B6.entries = true := by
  simp only [entryChecks,bflatBlockJ4B6,List.all_cons,List.all_nil,
    mode_checked_j4_m7,Bool.and_self]
theorem block_mass_checked_j4_b6 : blockMassCheck bflatBlockJ4B6 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
