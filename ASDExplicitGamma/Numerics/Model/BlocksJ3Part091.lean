module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part007
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part008

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B91 : ModeBlockData :=
  ⟨⟨127, 130, (1040787758097851233/10000000000000000000000 : ℚ), (198388221700118893/2500000000000000000000 : ℚ)⟩, [
    (127, modeDataJ3M128),
    (128, modeDataJ3M129),
    (129, modeDataJ3M130)], (104078775809785123/1000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b91 : entryChecks 3 bflatBlockJ3B91.entries = true := by
  simp only [entryChecks,bflatBlockJ3B91,List.all_cons,List.all_nil,
    mode_checked_j3_m128,
    mode_checked_j3_m129,
    mode_checked_j3_m130,Bool.and_self]
theorem block_mass_checked_j3_b91 : blockMassCheck bflatBlockJ3B91 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
