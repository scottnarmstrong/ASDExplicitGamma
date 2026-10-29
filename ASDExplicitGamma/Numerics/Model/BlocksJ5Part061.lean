module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part003

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B61 : ModeBlockData :=
  ⟨⟨61, 62, (24774422055896536143/10000000000000000000000 : ℚ), (39069941164633103/10000000000000000000000 : ℚ)⟩, [
    (61, modeDataJ5M62)], (12387211027948268071/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b61 : entryChecks 5 bflatBlockJ5B61.entries = true := by
  simp only [entryChecks,bflatBlockJ5B61,List.all_cons,List.all_nil,
    mode_checked_j5_m62,Bool.and_self]
theorem block_mass_checked_j5_b61 : blockMassCheck bflatBlockJ5B61 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
