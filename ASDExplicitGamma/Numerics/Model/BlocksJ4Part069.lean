module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part005

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B69 : ModeBlockData :=
  ⟨⟨85, 90, (54532236974090092469/2000000000000000000000 : ℚ), (1450813986274029043/10000000000000000000000 : ℚ)⟩, [
    (85, modeDataJ4M86),
    (86, modeDataJ4M87),
    (87, modeDataJ4M88),
    (88, modeDataJ4M89),
    (89, modeDataJ4M90)], (13633059243522523117/500000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b69 : entryChecks 4 bflatBlockJ4B69.entries = true := by
  simp only [entryChecks,bflatBlockJ4B69,List.all_cons,List.all_nil,
    mode_checked_j4_m86,
    mode_checked_j4_m87,
    mode_checked_j4_m88,
    mode_checked_j4_m89,
    mode_checked_j4_m90,Bool.and_self]
theorem block_mass_checked_j4_b69 : blockMassCheck bflatBlockJ4B69 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
