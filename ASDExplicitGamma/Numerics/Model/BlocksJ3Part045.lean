module
public import ASDExplicitGamma.Numerics.Model.BlockCertificate
public import ASDExplicitGamma.Numerics.Model.ModesJ3Part002

@[expose] public section
namespace ASDExplicitGamma.Numerics.Model
def bflatBlockJ3B45 : ModeBlockData :=
  ⟨⟨45, 46, (20037114886939260429/2000000000000000000000 : ℚ), (489626125489630927/2500000000000000000000 : ℚ)⟩, [
    (45, modeDataJ3M46)], (1565399600542129721/156250000000000000000 : ℚ)⟩

theorem block_entries_checked_j3_b45 : entryChecks 3 bflatBlockJ3B45.entries = true := by
  simp only [entryChecks,bflatBlockJ3B45,List.all_cons,List.all_nil,
    mode_checked_j3_m46,Bool.and_self]
theorem block_mass_checked_j3_b45 : blockMassCheck bflatBlockJ3B45 = true := by
  decide +kernel
end ASDExplicitGamma.Numerics.Model
