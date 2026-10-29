module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part004

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B64 : ModeBlockData :=
  ⟨⟨64, 71, (43197620428816097743/2500000000000000000000 : ℚ), (272858721974437619/10000000000000000000000 : ℚ)⟩, [
    (64, modeDataJ5M65),
    (65, modeDataJ5M66),
    (66, modeDataJ5M67),
    (67, modeDataJ5M68),
    (68, modeDataJ5M69),
    (69, modeDataJ5M70),
    (70, modeDataJ5M71)], (34558096343052878193/2000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b64 : entryChecks 5 bflatBlockJ5B64.entries = true := by
  simp only [entryChecks,bflatBlockJ5B64,List.all_cons,List.all_nil,
    mode_checked_j5_m65,
    mode_checked_j5_m66,
    mode_checked_j5_m67,
    mode_checked_j5_m68,
    mode_checked_j5_m69,
    mode_checked_j5_m70,
    mode_checked_j5_m71,Bool.and_self]
theorem block_mass_checked_j5_b64 : blockMassCheck bflatBlockJ5B64 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
