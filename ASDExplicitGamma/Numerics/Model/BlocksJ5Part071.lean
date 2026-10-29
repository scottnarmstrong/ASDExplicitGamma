module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ5Part008

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ5B71 : ModeBlockData :=
  ⟨⟨130, 144, (323308354413739938903/10000000000000000000000 : ℚ), (104652596772071327/2000000000000000000000 : ℚ)⟩, [
    (130, modeDataJ5M131),
    (131, modeDataJ5M132),
    (132, modeDataJ5M133),
    (133, modeDataJ5M134),
    (134, modeDataJ5M135),
    (135, modeDataJ5M136),
    (136, modeDataJ5M137),
    (137, modeDataJ5M138),
    (138, modeDataJ5M139),
    (139, modeDataJ5M140),
    (140, modeDataJ5M141),
    (141, modeDataJ5M142),
    (142, modeDataJ5M143),
    (143, modeDataJ5M144)], (323308354413739938889/10000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j5_b71 : entryChecks 5 bflatBlockJ5B71.entries = true := by
  simp only [entryChecks,bflatBlockJ5B71,List.all_cons,List.all_nil,
    mode_checked_j5_m131,
    mode_checked_j5_m132,
    mode_checked_j5_m133,
    mode_checked_j5_m134,
    mode_checked_j5_m135,
    mode_checked_j5_m136,
    mode_checked_j5_m137,
    mode_checked_j5_m138,
    mode_checked_j5_m139,
    mode_checked_j5_m140,
    mode_checked_j5_m141,
    mode_checked_j5_m142,
    mode_checked_j5_m143,
    mode_checked_j5_m144,Bool.and_self]
theorem block_mass_checked_j5_b71 : blockMassCheck bflatBlockJ5B71 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
