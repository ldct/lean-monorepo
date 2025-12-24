#!/usr/bin/env python3
"""
Check the progress of the SmallGroups project by comparing
existing files against the expected number of groups per order.
"""

from pathlib import Path
from collections import defaultdict

# Number of groups for each order (1-60)
# Source: https://people.maths.bris.ac.uk/~matyd/GroupNames/index.html
EXPECTED_GROUPS = {
    1: 1, 2: 1, 3: 1, 4: 2, 5: 1, 6: 2, 7: 1, 8: 5, 9: 2, 10: 2,
    11: 1, 12: 5, 13: 1, 14: 2, 15: 1, 16: 14, 17: 1, 18: 5, 19: 1, 20: 5,
    21: 2, 22: 2, 23: 1, 24: 15, 25: 2, 26: 2, 27: 5, 28: 4, 29: 1, 30: 4,
    31: 1, 32: 51, 33: 1, 34: 2, 35: 1, 36: 14, 37: 1, 38: 2, 39: 2, 40: 14,
    41: 1, 42: 6, 43: 1, 44: 4, 45: 2, 46: 2, 47: 1, 48: 52, 49: 2, 50: 5,
    51: 1, 52: 5, 53: 1, 54: 15, 55: 2, 56: 13, 57: 2, 58: 2, 59: 1, 60: 13,
}


def count_existing_groups():
    """Count existing Gap files by order."""
    smallgroups_dir = Path("Playground/Geometry/SmallGroups")
    counts = defaultdict(set)

    # Find all Gap_N directories
    for gap_dir in sorted(smallgroups_dir.glob("Gap_*")):
        if not gap_dir.is_dir():
            continue

        try:
            order = int(gap_dir.name.split("_")[1])
        except (IndexError, ValueError):
            continue

        # Count Gap_N_M.lean files in this directory
        for gap_file in gap_dir.glob("Gap_*.lean"):
            try:
                parts = gap_file.stem.split("_")
                if len(parts) >= 3:
                    gap_id = int(parts[2])
                    counts[order].add(gap_id)
            except (IndexError, ValueError):
                continue

    # Convert sets to counts
    return {order: len(ids) for order, ids in counts.items()}


def main():
    """Main function."""
    existing = count_existing_groups()

    print("SmallGroups Project Progress\n")
    print("=" * 70)

    # Calculate statistics
    complete_orders = []
    partial_orders = []
    missing_orders = []

    for order in sorted(EXPECTED_GROUPS.keys()):
        expected = EXPECTED_GROUPS[order]
        actual = existing.get(order, 0)

        if actual == expected:
            complete_orders.append(order)
        elif actual > 0:
            partial_orders.append((order, actual, expected))
        else:
            missing_orders.append(order)

    # Print complete orders
    if complete_orders:
        print(f"\n✓ Complete orders ({len(complete_orders)}):")
        for i in range(0, len(complete_orders), 10):
            batch = complete_orders[i:i+10]
            print(f"  {', '.join(str(o) for o in batch)}")

    # Print partial orders
    if partial_orders:
        print(f"\n⚠ Partial orders ({len(partial_orders)}):")
        for order, actual, expected in partial_orders:
            print(f"  Order {order:2d}: {actual}/{expected} groups")

    # Print missing orders
    if missing_orders:
        print(f"\n✗ Missing orders ({len(missing_orders)}):")
        for i in range(0, len(missing_orders), 10):
            batch = missing_orders[i:i+10]
            print(f"  {', '.join(str(o) for o in batch)}")

    # Summary statistics
    print("\n" + "=" * 70)
    total_expected = sum(EXPECTED_GROUPS.values())
    total_actual = sum(existing.values())
    percentage = (total_actual / total_expected * 100) if total_expected > 0 else 0

    print(f"\nSummary:")
    print(f"  Total groups: {total_actual}/{total_expected} ({percentage:.1f}%)")
    print(f"  Complete orders: {len(complete_orders)}/{len(EXPECTED_GROUPS)}")
    print(f"  Partial orders: {len(partial_orders)}")
    print(f"  Missing orders: {len(missing_orders)}")

    # Show next steps
    if partial_orders:
        print(f"\n📋 Next steps - Complete partial orders:")
        for order, actual, expected in partial_orders[:5]:
            missing = expected - actual
            print(f"  Order {order}: Add {missing} more group(s)")
    elif missing_orders:
        print(f"\n📋 Next steps - Start with order {missing_orders[0]} ({EXPECTED_GROUPS[missing_orders[0]]} group(s))")


if __name__ == "__main__":
    main()
