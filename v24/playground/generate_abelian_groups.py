#!/usr/bin/env python3
"""
Generate Lean files for non-cyclic abelian groups based on GAP IDs from GroupNames webpage.
Cyclic groups are excluded as they're already generated.
"""

from pathlib import Path

# Non-cyclic abelian groups with their GAP IDs and structure
# Format: order -> [(gap_id, name, lean_type), ...]
ABELIAN_GROUPS = {
    4: [(2, "C2_C2", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2)")],  # Already exists as Klein four-group
    8: [
        (2, "C4_C2", "Multiplicative (ZMod 4) × Multiplicative (ZMod 2)"),  # Already exists
        (5, "C2_C2_C2", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)"),  # Already exists
    ],
    9: [(2, "C3_C3", "Multiplicative (ZMod 3) × Multiplicative (ZMod 3)")],  # Already exists
    12: [(5, "C2_C6", "Multiplicative (ZMod 2) × Multiplicative (ZMod 6)")],
    16: [
        (2, "C4_C4", "Multiplicative (ZMod 4) × Multiplicative (ZMod 4)"),
        (5, "C2_C8", "Multiplicative (ZMod 2) × Multiplicative (ZMod 8)"),
        (10, "C2_C2_C4", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 4)"),
        (14, "C2_C2_C2_C2", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)"),
    ],
    18: [(5, "C3_C6", "Multiplicative (ZMod 3) × Multiplicative (ZMod 6)")],
    20: [(5, "C2_C10", "Multiplicative (ZMod 2) × Multiplicative (ZMod 10)")],
    24: [
        (9, "C2_C12", "Multiplicative (ZMod 2) × Multiplicative (ZMod 12)"),
        (15, "C2_C2_C6", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 6)"),
    ],
    25: [(2, "C5_C5", "Multiplicative (ZMod 5) × Multiplicative (ZMod 5)")],
    27: [
        (2, "C3_C9", "Multiplicative (ZMod 3) × Multiplicative (ZMod 9)"),
        (5, "C3_C3_C3", "Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 3)"),
    ],
    28: [(4, "C2_C14", "Multiplicative (ZMod 2) × Multiplicative (ZMod 14)")],
    32: [
        (3, "C4_C8", "Multiplicative (ZMod 4) × Multiplicative (ZMod 8)"),
        (5, "C2_C2_C8", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 8)"),
        (16, "C2_C16", "Multiplicative (ZMod 2) × Multiplicative (ZMod 16)"),
        (21, "C2_C4_C4", "Multiplicative (ZMod 2) × Multiplicative (ZMod 4) × Multiplicative (ZMod 4)"),
        (36, "C2_C2_C2_C4", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 4)"),
        (45, "C2_C2_C2_C2_C4", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 4)"),
        (51, "C2_C2_C2_C2_C2", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)"),
    ],
    36: [
        (5, "C2_C18", "Multiplicative (ZMod 2) × Multiplicative (ZMod 18)"),
        (8, "C3_C12", "Multiplicative (ZMod 3) × Multiplicative (ZMod 12)"),
        (14, "C6_C6", "Multiplicative (ZMod 6) × Multiplicative (ZMod 6)"),
    ],
    40: [
        (9, "C2_C20", "Multiplicative (ZMod 2) × Multiplicative (ZMod 20)"),
        (14, "C2_C2_C10", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 10)"),
    ],
    45: [(2, "C3_C15", "Multiplicative (ZMod 3) × Multiplicative (ZMod 15)")],
    48: [
        (20, "C4_C12", "Multiplicative (ZMod 4) × Multiplicative (ZMod 12)"),
        (23, "C2_C24", "Multiplicative (ZMod 2) × Multiplicative (ZMod 24)"),
        (44, "C2_C2_C12", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 12)"),
        (52, "C2_C2_C2_C6", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 6)"),
    ],
    50: [(5, "C5_C10", "Multiplicative (ZMod 5) × Multiplicative (ZMod 10)")],
    54: [
        (9, "C3_C18", "Multiplicative (ZMod 3) × Multiplicative (ZMod 18)"),
        (15, "C3_C3_C6", "Multiplicative (ZMod 3) × Multiplicative (ZMod 3) × Multiplicative (ZMod 6)"),
    ],
    56: [
        (8, "C2_C28", "Multiplicative (ZMod 2) × Multiplicative (ZMod 28)"),
        (13, "C2_C2_C14", "Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 14)"),
    ],
    60: [(13, "C2_C30", "Multiplicative (ZMod 2) × Multiplicative (ZMod 30)")],
}

LEAN_TEMPLATE = """import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev {name} := {lean_type}
"""


def main():
    """Generate all missing abelian group files."""
    base_dir = Path("Playground/Geometry/SmallGroups")
    created = []
    skipped = []

    for order, groups in sorted(ABELIAN_GROUPS.items()):
        for gap_id, name, lean_type in groups:
            # Create directory if needed
            gap_dir = base_dir / f"Gap_{order}"
            gap_dir.mkdir(parents=True, exist_ok=True)

            # Create file
            file_path = gap_dir / f"Gap_{order}_{gap_id}.lean"

            if file_path.exists():
                skipped.append((order, gap_id, name))
                continue

            content = LEAN_TEMPLATE.format(name=name, lean_type=lean_type)
            file_path.write_text(content)
            created.append((order, gap_id, name))

    # Report results
    print(f"Created {len(created)} abelian group files:")
    for order, gap_id, name in created:
        print(f"  Gap_{order}_{gap_id}.lean ({name}, order {order})")

    if skipped:
        print(f"\nSkipped {len(skipped)} existing files:")
        for order, gap_id, name in skipped:
            print(f"  Gap_{order}_{gap_id}.lean (already exists)")

    print(f"\nTotal: {len(created)} created, {len(skipped)} skipped")


if __name__ == "__main__":
    main()
