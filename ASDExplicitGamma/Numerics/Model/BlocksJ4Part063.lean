module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B63 : ModeBlockData :=
  ⟨⟨63, 64, (995424758235716229/156250000000000000000 : ℚ), (319179329807184537/10000000000000000000000 : ℚ)⟩, [
    (63, modeDataJ4M64)], (12741436905417167731/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b63 : entryChecks 4 bflatBlockJ4B63.entries = true := by
  simp only [entryChecks,bflatBlockJ4B63,List.all_cons,List.all_nil,
    mode_checked_j4_m64,Bool.and_self]
theorem block_mass_checked_j4_b63 : blockMassCheck bflatBlockJ4B63 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
