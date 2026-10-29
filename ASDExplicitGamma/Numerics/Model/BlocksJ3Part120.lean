module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part015

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B120 : ModeBlockData :=
  ⟨⟨244, 249, (69694798534679979/2000000000000000000000 : ℚ), (542114849024103/16000000000000000000 : ℚ)⟩, [
    (244, modeDataJ3M245),
    (245, modeDataJ3M246),
    (246, modeDataJ3M247),
    (247, modeDataJ3M248),
    (248, modeDataJ3M249)], (34847399267339989/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b120 : entryChecks 3 bflatBlockJ3B120.entries = true := by
  simp only [entryChecks,bflatBlockJ3B120,List.all_cons,List.all_nil,
    mode_checked_j3_m245,
    mode_checked_j3_m246,
    mode_checked_j3_m247,
    mode_checked_j3_m248,
    mode_checked_j3_m249,Bool.and_self]
theorem block_mass_checked_j3_b120 : blockMassCheck bflatBlockJ3B120 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
