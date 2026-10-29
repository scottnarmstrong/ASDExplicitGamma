module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part006

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B84 : ModeBlockData :=
  ⟨⟨106, 109, (2669127767458386081/10000000000000000000000 : ℚ), (1200847986731936803/10000000000000000000000 : ℚ)⟩, [
    (106, modeDataJ3M107),
    (107, modeDataJ3M108),
    (108, modeDataJ3M109)], (1334563883729193039/5000000000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b84 : entryChecks 3 bflatBlockJ3B84.entries = true := by
  simp only [entryChecks,bflatBlockJ3B84,List.all_cons,List.all_nil,
    mode_checked_j3_m107,
    mode_checked_j3_m108,
    mode_checked_j3_m109,Bool.and_self]
theorem block_mass_checked_j3_b84 : blockMassCheck bflatBlockJ3B84 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
