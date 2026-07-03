#!/usr/bin/env python3
"""
Generate centralized evaluation files for SmallGroups project.
"""

import re
from pathlib import Path

def parse_smallgroups_abbrevs():
    """Parse SmallGroups.lean to get list of all group abbrev names."""
    smallgroups_file = Path("Playground/Geometry/SmallGroups/SmallGroups.lean")
    abbrev_names = []

    with open(smallgroups_file, 'r') as f:
        for line in f:
            line = line.strip()
            # Skip comments and imports
            if line.startswith('--') or line.startswith('import') or line.startswith('set_option'):
                continue
            # Match abbrev statements: abbrev GroupName := ...
            match = re.match(r'abbrev\s+(\w+)\s+:=', line)
            if match:
                abbrev_names.append(match.group(1))

    return abbrev_names

def generate_eval_file(property_name, eval_expr, group_names, output_file, postfix=""):
    """Generate a centralized evaluation file for a property."""
    lines = [
        "import Playground.Geometry.SmallGroups.SmallGroups",
        "import Playground.Geometry.SmallGroups.GroupProps",
        "",
        "set_option linter.style.setOption false",
        "set_option maxHeartbeats 2000000"
    ]

    lines.extend([
        "def main : IO Unit := do",
        "  let values := [",
    ])

    for i, group_name in enumerate(group_names):
        comma = "," if i < len(group_names) - 1 else ""
        if postfix:
            lines.append(f"  ({eval_expr} {group_name}){postfix}{comma}")
        else:
            lines.append(f"  {eval_expr} {group_name}{comma}")

    lines.append("  ]")
    lines.append("  IO.println (repr values)")
    lines.append("")  # Empty line at end

    with open(output_file, 'w') as f:
        f.write('\n'.join(lines))

    print(f"Generated {output_file} with {len(group_names)} evaluations")

def main():
    """Main function to generate all evaluation files."""
    # Parse abbrev names directly from SmallGroups.lean
    group_names = parse_smallgroups_abbrevs()
    print(f"Found {len(group_names)} group definitions")

    for name in group_names:
        print(f"  {name}")

    # Generate the 6 evaluation files
    base_path = Path("Playground/Geometry/SmallGroups")

    properties = [
        ("Cardinality", "Fintype.card", "EvalCardinality.lean", ""),
        ("IsAbelian", "Group.IsAbelian", "EvalAbelian.lean", ""),
        ("FracInvolutions", "Group.FracInvolutions", "EvalFracInvolutions.lean", ""),
        ("CommutingFraction", "Group.CommutingFraction", "EvalCommutingFraction.lean", ""),
        ("NumSubgroups", "Group.numSubgroups", "EvalNumSubgroups.lean", ""),
        ("Z1Size", "Z1Size", "EvalZ1Size.lean", ""),
        ("Z2Size", "Z2Size", "EvalZ2Size.lean", ""),
        ("Z3Size", "Z3Size", "EvalZ3Size.lean", ""),
        ("Z4Size", "Z4Size", "EvalZ4Size.lean", ""),
        ("Exponent", "Group.exponent", "EvalExponent.lean", ".val"),
    ]

    for prop_name, eval_expr, filename, postfix in properties:
        output_file = base_path / filename
        generate_eval_file(prop_name, eval_expr, group_names, output_file, postfix)

    print("\n✅ Successfully generated all evaluation files")

if __name__ == "__main__":
    main()
