module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part006

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B85 : ModeBlockData :=
  ⟨⟨109, 112, (241918622367385813/1250000000000000000000 : ℚ), (56174444420474609/500000000000000000000 : ℚ)⟩, [
    (109, modeDataJ3M110),
    (110, modeDataJ3M111),
    (111, modeDataJ3M112)], (1935348978939086501/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b85 : entryChecks 3 bflatBlockJ3B85.entries = true := by
  simp only [entryChecks,bflatBlockJ3B85,List.all_cons,List.all_nil,
    mode_checked_j3_m110,
    mode_checked_j3_m111,
    mode_checked_j3_m112,Bool.and_self]
theorem block_mass_checked_j3_b85 : blockMassCheck bflatBlockJ3B85 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
