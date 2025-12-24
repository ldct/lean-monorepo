#!/usr/bin/env python3
"""
Generate Lean files for all groups in the SmallGroups project.
Consolidated generator handling cyclic, dihedral, abelian, and direct product groups.
Based on GAP IDs from GroupNames webpage.

Contains all 150 groups from orders 1-60, including:
- Cyclic groups (ℤₙ)
- Dihedral groups (Dₙ)
- Abelian products (direct products of cyclic groups)
- Special groups (S₃, S₄, A₄, A₅, Q₈)
"""

from pathlib import Path

# All groups with their GAP IDs and Lean types
# Format: order -> [(gap_id, name, lean_type, description), ...]
DIRECT_PRODUCTS = {
    # Order 1
    1: [
        (1, "Trivial", "Multiplicative (ZMod 1)", "ℤ₁"),
    ],
    # Order 2
    2: [
        (1, "Z2", "Multiplicative (ZMod 2)", "ℤ₂"),
    ],
    # Order 3
    3: [
        (1, "Z3", "Multiplicative (ZMod 3)", "ℤ₃"),
    ],
    # Order 4
    4: [
        (1, "Z4", "Multiplicative (ZMod 4)", "ℤ₄"),
        (2, "V4", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2)", "C₂ × C₂"),
    ],
    # Order 5
    5: [
        (1, "Z5", "Multiplicative (ZMod 5)", "ℤ₅"),
    ],
    # Order 6
    6: [
        (1, "S3", "Equiv.Perm (Fin 3)", "S₃"),  # Also known as Dih3
        (2, "Z6", "Multiplicative (ZMod 6)", "ℤ₆"),
    ],
    # Order 7
    7: [
        (1, "Z7", "Multiplicative (ZMod 7)", "ℤ₇"),
    ],
    # Order 8
    8: [
        (1, "Z8", "Multiplicative (ZMod 8)", "ℤ₈"),
        (2, "C4_C2", "Multiplicative (ZMod 4) × Multiplicative (ZMod 2)", "C₄ × C₂"),
        (3, "Dih4", "DihedralGroup 4", "D₄"),
        (4, "Q", "QuaternionGroup 2", "Q₈"),
        (5, "E8", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)", "C₂ × C₂ × C₂"),
    ],
    # Order 9
    9: [
        (1, "Z9", "Multiplicative (ZMod 9)", "ℤ₉"),
        (2, "E9", "Multiplicative (ZMod 3) × Multiplicative (ZMod 3)", "C₃ × C₃"),
    ],
    # Order 10
    10: [
        (1, "Dih5", "DihedralGroup 5", "D₅"),
        (2, "Z10", "Multiplicative (ZMod 10)", "ℤ₁₀"),
    ],
    # Order 11
    11: [
        (1, "Z11", "Multiplicative (ZMod 11)", "ℤ₁₁"),
    ],
    # Order 12
    12: [
        (1, "Z12", "Multiplicative (ZMod 12)", "ℤ₁₂"),
        (3, "A4", "AlternatingGroup 4", "A₄"),
        (4, "Dih6", "DihedralGroup 6", "D₆"),
        (5, "C2_C6", "Multiplicative (ZMod 2) × Multiplicative (ZMod 6)", "C₂ × C₆"),
    ],
    # Order 13
    13: [
        (1, "Z13", "Multiplicative (ZMod 13)", "ℤ₁₃"),
    ],
    # Order 14
    14: [
        (1, "Dih7", "DihedralGroup 7", "D₇"),
        (2, "Z14", "Multiplicative (ZMod 14)", "ℤ₁₄"),
    ],
    # Order 15
    15: [
        (1, "Z15", "Multiplicative (ZMod 15)", "ℤ₁₅"),
    ],
    # Order 16
    16: [
        (1, "Z16", "Multiplicative (ZMod 16)", "ℤ₁₆"),
        (2, "C4_C4", "Multiplicative (ZMod 4) × Multiplicative (ZMod 4)", "C₄ × C₄"),
        (5, "C2_C8", "Multiplicative (ZMod 2) × Multiplicative (ZMod 8)", "C₂ × C₈"),
        (7, "Dih8", "DihedralGroup 8", "D₈"),
        (10, "C2_C2_C4", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 4)", "C₂ × C₂ × C₄"),
        (11, "C2_Dih4", "Multiplicative (ZMod 2) × DihedralGroup 4", "C₂ × D₄"),
        (12, "C2_Q", "Multiplicative (ZMod 2) × QuaternionGroup 2", "C₂ × Q₈"),
        (14, "C2_C2_C2_C2", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)", "C₂ × C₂ × C₂ × C₂"),
    ],
    # Order 17
    17: [
        (1, "Z17", "Multiplicative (ZMod 17)", "ℤ₁₇"),
    ],
    # Order 18
    18: [
        (1, "Dih9", "DihedralGroup 9", "D₉"),
        (2, "Z18", "Multiplicative (ZMod 18)", "ℤ₁₈"),
        (3, "C3_S3", "Multiplicative (ZMod 3) × Equiv.Perm (Fin 3)", "C₃ × S₃"),
        (5, "C3_C6", "Multiplicative (ZMod 3) × Multiplicative (ZMod 6)", "C₃ × C₆"),
    ],
    # Order 19
    19: [
        (1, "Z19", "Multiplicative (ZMod 19)", "ℤ₁₉"),
    ],
    # Order 20
    20: [
        (2, "Z20", "Multiplicative (ZMod 20)", "ℤ₂₀"),
        (4, "Dih10", "DihedralGroup 10", "D₁₀"),
        (5, "C2_C10", "Multiplicative (ZMod 2) × Multiplicative (ZMod 10)", "C₂ × C₁₀"),
    ],
    # Order 21
    21: [
        (2, "Z21", "Multiplicative (ZMod 21)", "ℤ₂₁"),
    ],
    # Order 22
    22: [
        (1, "Dih11", "DihedralGroup 11", "D₁₁"),
        (2, "Z22", "Multiplicative (ZMod 22)", "ℤ₂₂"),
    ],
    # Order 23
    23: [
        (1, "Z23", "Multiplicative (ZMod 23)", "ℤ₂₃"),
    ],
    # Order 24
    24: [
        (2, "Z24", "Multiplicative (ZMod 24)", "ℤ₂₄"),
        (5, "C4_S3", "Multiplicative (ZMod 4) × Equiv.Perm (Fin 3)", "C₄ × S₃"),
        (6, "Dih12", "DihedralGroup 12", "D₁₂"),
        (9, "C2_C12", "Multiplicative (ZMod 2) × Multiplicative (ZMod 12)", "C₂ × C₁₂"),
        (10, "C3_Dih4", "Multiplicative (ZMod 3) × DihedralGroup 4", "C₃ × D₄"),
        (11, "C3_Q", "Multiplicative (ZMod 3) × QuaternionGroup 2", "C₃ × Q₈"),
        (12, "S4", "Equiv.Perm (Fin 4)", "S₄"),
        (13, "C2_A4", "Multiplicative (ZMod 2) × AlternatingGroup 4", "C₂ × A₄"),
        (14, "C2_C2_S3", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)", "C₂ × C₂ × S₃"),
        (15, "C2_C2_C6", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 6)", "C₂ × C₂ × C₆"),
    ],
    # Order 25
    25: [
        (1, "Z25", "Multiplicative (ZMod 25)", "ℤ₂₅"),
        (2, "C5_C5", "Multiplicative (ZMod 5) × Multiplicative (ZMod 5)", "C₅ × C₅"),
    ],
    # Order 26
    26: [
        (1, "Dih13", "DihedralGroup 13", "D₁₃"),
        (2, "Z26", "Multiplicative (ZMod 26)", "ℤ₂₆"),
    ],
    # Order 27
    27: [
        (1, "Z27", "Multiplicative (ZMod 27)", "ℤ₂₇"),
        (2, "C3_C9", "Multiplicative (ZMod 3) × Multiplicative (ZMod 9)", "C₃ × C₉"),
        (5, "C3_C3_C3", "Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3)", "C₃ × C₃ × C₃"),
    ],
    # Order 28
    28: [
        (2, "Z28", "Multiplicative (ZMod 28)", "ℤ₂₈"),
        (3, "Dih14", "DihedralGroup 14", "D₁₄"),
        (4, "C2_C14", "Multiplicative (ZMod 2) × Multiplicative (ZMod 14)", "C₂ × C₁₄"),
    ],
    # Order 29
    29: [
        (1, "Z29", "Multiplicative (ZMod 29)", "ℤ₂₉"),
    ],
    # Order 30
    30: [
        (1, "S3_C5", "Equiv.Perm (Fin 3) × Multiplicative (ZMod 5)", "S₃ × C₅"),
        (2, "C5_S3", "Multiplicative (ZMod 5) × Equiv.Perm (Fin 3)", "C₅ × S₃"),
        (3, "Dih15", "DihedralGroup 15", "D₁₅"),
        (4, "Z30", "Multiplicative (ZMod 30)", "ℤ₃₀"),
    ],
    # Order 31
    31: [
        (1, "Z31", "Multiplicative (ZMod 31)", "ℤ₃₁"),
    ],
    # Order 32
    32: [
        (1, "Z32", "Multiplicative (ZMod 32)", "ℤ₃₂"),
        (3, "C4_C8", "Multiplicative (ZMod 4) × Multiplicative (ZMod 8)", "C₄ × C₈"),
        (5, "C2_C2_C8", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 8)", "C₂ × C₂ × C₈"),
        (16, "C2_C16", "Multiplicative (ZMod 2) × Multiplicative (ZMod 16)", "C₂ × C₁₆"),
        (18, "Dih16", "DihedralGroup 16", "D₁₆"),
        (21, "C2_C4_C4", "Multiplicative (ZMod 2) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4)", "C₂ × C₄ × C₄"),
        (36, "C2_C2_C2_C4", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 4)", "C₂ × C₂ × C₂ × C₄"),
        (39, "C2_Dih8", "Multiplicative (ZMod 2) × DihedralGroup 8", "C₂ × D₈"),
    ],
    # Order 33
    33: [
        (1, "Z33", "Multiplicative (ZMod 33)", "ℤ₃₃"),
    ],
    # Order 34
    34: [
        (1, "Dih17", "DihedralGroup 17", "D₁₇"),
        (2, "Z34", "Multiplicative (ZMod 34)", "ℤ₃₄"),
    ],
    # Order 35
    35: [
        (1, "Z35", "Multiplicative (ZMod 35)", "ℤ₃₅"),
    ],
    # Order 36
    36: [
        (2, "Z36", "Multiplicative (ZMod 36)", "ℤ₃₆"),
        (4, "Dih18", "DihedralGroup 18", "D₁₈"),
        (5, "C2_C18", "Multiplicative (ZMod 2) × Multiplicative (ZMod 18)", "C₂ × C₁₈"),
        (8, "C3_C12", "Multiplicative (ZMod 3) × Multiplicative (ZMod 12)", "C₃ × C₁₂"),
        (10, "C3_Dih6", "Multiplicative (ZMod 3) × DihedralGroup 6", "C₃ × D₆"),
        (14, "C6_C6", "Multiplicative (ZMod 6) × Multiplicative (ZMod 6)", "C₆ × C₆"),
    ],
    # Order 37
    37: [
        (1, "Z37", "Multiplicative (ZMod 37)", "ℤ₃₇"),
    ],
    # Order 38
    38: [
        (1, "Dih19", "DihedralGroup 19", "D₁₉"),
        (2, "Z38", "Multiplicative (ZMod 38)", "ℤ₃₈"),
    ],
    # Order 39
    39: [
        (1, "Z39", "Multiplicative (ZMod 39)", "ℤ₃₉"),
    ],
    # Order 40
    40: [
        (2, "Z40", "Multiplicative (ZMod 40)", "ℤ₄₀"),
        (5, "C4_Dih5", "Multiplicative (ZMod 4) × DihedralGroup 5", "C₄ × D₅"),
        (6, "Dih20", "DihedralGroup 20", "D₂₀"),
        (7, "C2_C20", "Multiplicative (ZMod 2) × Multiplicative (ZMod 20)", "C₂ × C₂₀"),
        (10, "C5_Dih4", "Multiplicative (ZMod 5) × DihedralGroup 4", "C₅ × D₄"),
        (12, "C2_C2_C10", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 10)", "C₂ × C₂ × C₁₀"),
    ],
    # Order 41
    41: [
        (1, "Z41", "Multiplicative (ZMod 41)", "ℤ₄₁"),
    ],
    # Order 42
    42: [
        (3, "C7_S3", "Multiplicative (ZMod 7) × Equiv.Perm (Fin 3)", "C₇ × S₃"),
        (5, "Dih21", "DihedralGroup 21", "D₂₁"),
        (6, "Z42", "Multiplicative (ZMod 42)", "ℤ₄₂"),
    ],
    # Order 43
    43: [
        (1, "Z43", "Multiplicative (ZMod 43)", "ℤ₄₃"),
    ],
    # Order 44
    44: [
        (2, "Z44", "Multiplicative (ZMod 44)", "ℤ₄₄"),
        (3, "Dih22", "DihedralGroup 22", "D₂₂"),
    ],
    # Order 45
    45: [
        (1, "Z45", "Multiplicative (ZMod 45)", "ℤ₄₅"),
        (2, "C3_C15", "Multiplicative (ZMod 3) × Multiplicative (ZMod 15)", "C₃ × C₁₅"),
    ],
    # Order 46
    46: [
        (1, "Dih23", "DihedralGroup 23", "D₂₃"),
        (2, "Z46", "Multiplicative (ZMod 46)", "ℤ₄₆"),
    ],
    # Order 47
    47: [
        (1, "Z47", "Multiplicative (ZMod 47)", "ℤ₄₇"),
    ],
    # Order 48
    48: [
        (2, "Z48", "Multiplicative (ZMod 48)", "ℤ₄₈"),
        (3, "C4_C12", "Multiplicative (ZMod 4) × Multiplicative (ZMod 12)", "C₄ × C₁₂"),
        (5, "C2_C24", "Multiplicative (ZMod 2) × Multiplicative (ZMod 24)", "C₂ × C₂₄"),
        (7, "Dih24", "DihedralGroup 24", "D₂₄"),
        (15, "C2_C2_C12", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 12)", "C₂ × C₂ × C₁₂"),
        (31, "C4_A4", "Multiplicative (ZMod 4) × AlternatingGroup 4", "C₄ × A₄"),
        (48, "C2_S4", "Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)", "C₂ × S₄"),
        (50, "C2_C2_C2_C6", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 6)", "C₂ × C₂ × C₂ × C₆"),
    ],
    # Order 49
    49: [
        (1, "Z49", "Multiplicative (ZMod 49)", "ℤ₄₉"),
    ],
    # Order 50
    50: [
        (1, "Dih25", "DihedralGroup 25", "D₂₅"),
        (2, "Z50", "Multiplicative (ZMod 50)", "ℤ₅₀"),
        (3, "C5_Dih5", "Multiplicative (ZMod 5) × DihedralGroup 5", "C₅ × D₅"),
        (5, "C5_C10", "Multiplicative (ZMod 5) × Multiplicative (ZMod 10)", "C₅ × C₁₀"),
    ],
    # Order 51
    51: [
        (1, "Z51", "Multiplicative (ZMod 51)", "ℤ₅₁"),
    ],
    # Order 52
    52: [
        (2, "Z52", "Multiplicative (ZMod 52)", "ℤ₅₂"),
        (4, "Dih26", "DihedralGroup 26", "D₂₆"),
    ],
    # Order 53
    53: [
        (1, "Z53", "Multiplicative (ZMod 53)", "ℤ₅₃"),
    ],
    # Order 54
    54: [
        (1, "Dih27", "DihedralGroup 27", "D₂₇"),
        (2, "Z54", "Multiplicative (ZMod 54)", "ℤ₅₄"),
        (4, "C3_C18", "Multiplicative (ZMod 3) × Multiplicative (ZMod 18)", "C₃ × C₁₈"),
        (5, "C3_Dih9", "Multiplicative (ZMod 3) × DihedralGroup 9", "C₃ × D₉"),
        (15, "C3_C3_C6", "Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 6)", "C₃ × C₃ × C₆"),
    ],
    # Order 55
    55: [
        (2, "Z55", "Multiplicative (ZMod 55)", "ℤ₅₅"),
    ],
    # Order 56
    56: [
        (2, "Z56", "Multiplicative (ZMod 56)", "ℤ₅₆"),
        (4, "C2_C28", "Multiplicative (ZMod 2) × Multiplicative (ZMod 28)", "C₂ × C₂₈"),
        (5, "Dih28", "DihedralGroup 28", "D₂₈"),
        (11, "C2_C2_C14", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 14)", "C₂ × C₂ × C₁₄"),
    ],
    # Order 57
    57: [
        (2, "Z57", "Multiplicative (ZMod 57)", "ℤ₅₇"),
    ],
    # Order 58
    58: [
        (1, "Dih29", "DihedralGroup 29", "D₂₉"),
        (2, "Z58", "Multiplicative (ZMod 58)", "ℤ₅₈"),
    ],
    # Order 59
    59: [
        (1, "Z59", "Multiplicative (ZMod 59)", "ℤ₅₉"),
    ],
    # Order 60
    60: [
        (4, "Z60", "Multiplicative (ZMod 60)", "ℤ₆₀"),
        (5, "A5", "AlternatingGroup 5", "A₅"),
        (6, "C2_C30", "Multiplicative (ZMod 2) × Multiplicative (ZMod 30)", "C₂ × C₃₀"),
        (9, "C5_A4", "Multiplicative (ZMod 5) × AlternatingGroup 4", "C₅ × A₄"),
        (12, "Dih30", "DihedralGroup 30", "D₃₀"),
    ],
}

LEAN_TEMPLATE = """import Mathlib
import Playground.Geometry.SmallGroups.GroupProps{alternating_import}

abbrev {name} := {lean_type}{quaternion_deriving}
"""


def main():
    """Generate all group files (cyclic, dihedral, abelian, and direct products)."""
    base_dir = Path("Playground/Geometry/SmallGroups")
    created = []
    skipped = []

    # Generate all groups
    for order, groups in sorted(DIRECT_PRODUCTS.items()):
        for gap_id, name, lean_type, description in groups:
            # Create directory if needed
            gap_dir = base_dir / f"Gap_{order}"
            gap_dir.mkdir(parents=True, exist_ok=True)

            # Create file
            file_path = gap_dir / f"Gap_{order}_{gap_id}.lean"

            if file_path.exists():
                skipped.append((order, gap_id, name, description))
                print(f"⚠️  Skipping {file_path.name} - already exists")
                continue

            # Determine conditional template parts
            alternating_import = "\nimport Playground.Geometry.SmallGroups.AlternatingGroup" if "AlternatingGroup" in lean_type else ""
            quaternion_deriving = "\n\nderiving instance Repr for QuaternionGroup" if "QuaternionGroup" in lean_type else ""

            content = LEAN_TEMPLATE.format(
                name=name,
                lean_type=lean_type,
                alternating_import=alternating_import,
                quaternion_deriving=quaternion_deriving
            )
            file_path.write_text(content)
            created.append((order, gap_id, name, description))
            print(f"✓ Created {file_path.name}: {description}")

    # Report results
    print(f"\n{'='*60}")
    print(f"Created {len(created)} group files")

    if created:
        print(f"\nNew groups:")
        for order, gap_id, name, description in created:
            print(f"  Gap({order},{gap_id}): {description} - {name}")

    if skipped:
        print(f"\n⚠️  Skipped {len(skipped)} existing files")

    print(f"\nTotal: {len(created)} created, {len(skipped)} skipped")

    if created:
        print(f"\n⚠️  IMPORTANT: You need to:")
        print(f"  1. Add imports to SmallGroups.lean: python3 update_smallgroups_imports.py")
        print(f"  2. Regenerate evaluation files: python3 generate_eval_files.py")


if __name__ == "__main__":
    main()
