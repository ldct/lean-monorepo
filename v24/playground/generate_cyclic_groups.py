#!/usr/bin/env python3
"""
Generate Lean files for cyclic groups based on GAP IDs from GroupNames webpage.
"""

from pathlib import Path

# Cyclic groups with their GAP IDs from https://people.maths.bris.ac.uk/~matyd/GroupNames/index.html
CYCLIC_GROUPS = {
    13: 1, 14: 2, 15: 1, 16: 1, 17: 1, 18: 2, 19: 1, 20: 2,
    21: 2, 22: 2, 23: 1, 24: 2, 25: 1, 26: 2, 27: 1, 28: 2,
    29: 1, 30: 4, 31: 1, 32: 1, 33: 1, 34: 2, 35: 1, 36: 2,
    37: 1, 38: 2, 39: 1, 40: 2, 41: 1, 42: 6, 43: 1, 44: 2,
    45: 1, 46: 2, 47: 1, 48: 2, 49: 1, 50: 2, 51: 1, 52: 2,
    53: 1, 54: 2, 55: 2, 56: 2, 57: 2, 58: 2, 59: 1, 60: 4,
}

LEAN_TEMPLATE = """import Mathlib
import Playground.Geometry.SmallGroups.GroupProps

abbrev Z{order} := Multiplicative (ZMod {order})
"""


def main():
    """Generate all missing cyclic group files."""
    base_dir = Path("Playground/Geometry/SmallGroups")
    created = []
    skipped = []

    for order, gap_id in sorted(CYCLIC_GROUPS.items()):
        # Create directory if needed
        gap_dir = base_dir / f"Gap_{order}"
        gap_dir.mkdir(parents=True, exist_ok=True)

        # Create file
        file_path = gap_dir / f"Gap_{order}_{gap_id}.lean"

        if file_path.exists():
            skipped.append((order, gap_id))
            continue

        content = LEAN_TEMPLATE.format(order=order)
        file_path.write_text(content)
        created.append((order, gap_id))

    # Report results
    print(f"Created {len(created)} cyclic group files:")
    for order, gap_id in created:
        print(f"  Gap_{order}_{gap_id}.lean (Z{order})")

    if skipped:
        print(f"\nSkipped {len(skipped)} existing files:")
        for order, gap_id in skipped:
            print(f"  Gap_{order}_{gap_id}.lean (already exists)")

    print(f"\nTotal: {len(created)} created, {len(skipped)} skipped")


if __name__ == "__main__":
    main()
