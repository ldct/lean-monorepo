#!/usr/bin/env python3
"""
Generate Lean files for direct product groups based on GAP IDs from GroupNames webpage.
Focuses on non-abelian direct products (abelian ones are already covered).
"""

from pathlib import Path

# Direct product groups with their GAP IDs and Lean types
# Format: order -> [(gap_id, name, lean_type, description), ...]
DIRECT_PRODUCTS = {
    # Order 16
    16: [
        (11, "C2_Dih4", "Multiplicative (ZMod 2) × DihedralGroup 4", "C₂ × D₄"),
        (12, "C2_Q", "Multiplicative (ZMod 2) × QuaternionGroup 2", "C₂ × Q₈"),
    ],
    # Order 18
    18: [
        (3, "C3_S3", "Multiplicative (ZMod 3) × Equiv.Perm (Fin 3)", "C₃ × S₃"),
    ],
    # Order 24
    24: [
        (5, "C4_S3", "Multiplicative (ZMod 4) × Equiv.Perm (Fin 3)", "C₄ × S₃"),
        (10, "C3_Dih4", "Multiplicative (ZMod 3) × DihedralGroup 4", "C₃ × D₄"),
        (11, "C3_Q", "Multiplicative (ZMod 3) × QuaternionGroup 2", "C₃ × Q₈"),
        (13, "C2_A4", "Multiplicative (ZMod 2) × AlternatingGroup 4", "C₂ × A₄"),
        (14, "C2_C2_S3", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Equiv.Perm (Fin 3)", "C₂ × C₂ × S₃"),
    ],
    # Order 30
    30: [
        (1, "S3_C5", "Equiv.Perm (Fin 3) × Multiplicative (ZMod 5)", "S₃ × C₅"),
        (2, "C5_S3", "Multiplicative (ZMod 5) × Equiv.Perm (Fin 3)", "C₅ × S₃"),
    ],
    # Order 32
    32: [
        (39, "C2_Dih8", "Multiplicative (ZMod 2) × DihedralGroup 8", "C₂ × D₈"),
    ],
    # Order 36
    36: [
        (10, "C3_Dih6", "Multiplicative (ZMod 3) × DihedralGroup 6", "C₃ × D₆"),
    ],
    # Order 40
    40: [
        (5, "C4_Dih5", "Multiplicative (ZMod 4) × DihedralGroup 5", "C₄ × D₅"),
        (10, "C5_Dih4", "Multiplicative (ZMod 5) × DihedralGroup 4", "C₅ × D₄"),
    ],
    # Order 42
    42: [
        (3, "C7_S3", "Multiplicative (ZMod 7) × Equiv.Perm (Fin 3)", "C₇ × S₃"),
    ],
    # Order 48
    48: [
        (31, "C4_A4", "Multiplicative (ZMod 4) × AlternatingGroup 4", "C₄ × A₄"),
        (48, "C2_S4", "Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)", "C₂ × S₄"),
    ],
    # Order 50
    50: [
        (3, "C5_Dih5", "Multiplicative (ZMod 5) × DihedralGroup 5", "C₅ × D₅"),
    ],
    # Order 54
    54: [
        (5, "C3_Dih9", "Multiplicative (ZMod 3) × DihedralGroup 9", "C₃ × D₉"),
    ],
    # Order 60
    60: [
        (9, "C5_A4", "Multiplicative (ZMod 5) × AlternatingGroup 4", "C₅ × A₄"),
    ],
}

LEAN_TEMPLATE_BASIC = """import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev {name} := {lean_type}
"""

LEAN_TEMPLATE_ALTERNATING = """import Mathlib
import Playground.Geometry.SmallGroups.GroupProps
import Playground.Geometry.SmallGroups.AlternatingGroup

abbrev {name} := {lean_type}
"""


def main():
    """Generate all direct product group files."""
    base_dir = Path("Playground/Geometry/SmallGroups")
    created = []
    skipped = []

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

            # Choose template based on whether AlternatingGroup is used
            if "AlternatingGroup" in lean_type:
                template = LEAN_TEMPLATE_ALTERNATING
            else:
                template = LEAN_TEMPLATE_BASIC

            content = template.format(name=name, lean_type=lean_type)
            file_path.write_text(content)
            created.append((order, gap_id, name, description))
            print(f"✓ Created {file_path.name}: {description}")

    # Report results
    print(f"\n{'='*60}")
    print(f"Created {len(created)} direct product group files")

    if created:
        print(f"\nNew groups:")
        for order, gap_id, name, description in created:
            print(f"  Gap({order},{gap_id}): {description} - {name}")

    if skipped:
        print(f"\n⚠️  Skipped {len(skipped)} existing files")

    print(f"\nTotal: {len(created)} created, {len(skipped)} skipped")

    if created:
        print(f"\n⚠️  IMPORTANT: You need to:")
        print(f"  1. Add imports to SmallGroups.lean")
        print(f"  2. Regenerate evaluation files: python3 generate_eval_files.py")


if __name__ == "__main__":
    main()
