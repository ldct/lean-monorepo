#!/usr/bin/env python3
"""
Generate Lean files for dihedral groups based on GAP IDs from GroupNames webpage.
"""

from pathlib import Path

# Dihedral groups with their GAP IDs from https://people.maths.bris.ac.uk/~matyd/GroupNames/index.html
# Order -> (GAP_ID, n) where DihedralGroup n has order 2n
DIHEDRAL_GROUPS = {
    6: (1, 3),     # D3
    10: (1, 5),    # D5 (already exists as Gap_10_1)
    12: (4, 6),    # D6
    14: (1, 7),    # D7
    16: (7, 8),    # D8
    18: (1, 9),    # D9
    20: (4, 10),   # D10
    22: (1, 11),   # D11
    24: (6, 12),   # D12
    26: (1, 13),   # D13
    28: (3, 14),   # D14
    30: (3, 15),   # D15
    32: (18, 16),  # D16
    34: (1, 17),   # D17
    36: (4, 18),   # D18
    38: (1, 19),   # D19
    40: (6, 20),   # D20
    42: (5, 21),   # D21
    44: (3, 22),   # D22
    46: (1, 23),   # D23
    48: (7, 24),   # D24
    50: (1, 25),   # D25
    52: (4, 26),   # D26
    54: (1, 27),   # D27
    56: (5, 28),   # D28
    58: (1, 29),   # D29
    60: (12, 30),  # D30
}

LEAN_TEMPLATE = """import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Dih{n} := DihedralGroup {n}
"""


def main():
    """Generate all missing dihedral group files."""
    base_dir = Path("Playground/Geometry/SmallGroups")
    created = []
    skipped = []

    for order, (gap_id, n) in sorted(DIHEDRAL_GROUPS.items()):
        # Create directory if needed
        gap_dir = base_dir / f"Gap_{order}"
        gap_dir.mkdir(parents=True, exist_ok=True)

        # Create file
        file_path = gap_dir / f"Gap_{order}_{gap_id}.lean"

        # Always overwrite to ensure consistent naming
        content = LEAN_TEMPLATE.format(n=n)
        file_path.write_text(content)
        created.append((order, gap_id, n))

    # Report results
    print(f"Created {len(created)} dihedral group files:")
    for order, gap_id, n in created:
        print(f"  Gap_{order}_{gap_id}.lean (D{n}, order {order})")

    if skipped:
        print(f"\nSkipped {len(skipped)} existing files:")
        for order, gap_id, n in skipped:
            print(f"  Gap_{order}_{gap_id}.lean (already exists)")

    print(f"\nTotal: {len(created)} created, {len(skipped)} skipped")


if __name__ == "__main__":
    main()
