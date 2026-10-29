module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ4Part006

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ4B73 : ModeBlockData :=
  ⟨⟨106, 112, (68062723218760825137/2500000000000000000000 : ℚ), (312074568246532979/2000000000000000000000 : ℚ)⟩, [
    (106, modeDataJ4M107),
    (107, modeDataJ4M108),
    (108, modeDataJ4M109),
    (109, modeDataJ4M110),
    (110, modeDataJ4M111),
    (111, modeDataJ4M112)], (136125446437521650271/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j4_b73 : entryChecks 4 bflatBlockJ4B73.entries = true := by
  simp only [entryChecks,bflatBlockJ4B73,List.all_cons,List.all_nil,
    mode_checked_j4_m107,
    mode_checked_j4_m108,
    mode_checked_j4_m109,
    mode_checked_j4_m110,
    mode_checked_j4_m111,
    mode_checked_j4_m112,Bool.and_self]
theorem block_mass_checked_j4_b73 : blockMassCheck bflatBlockJ4B73 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
