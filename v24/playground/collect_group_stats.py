#!/usr/bin/env python3
"""
Collect group statistics by running lake build on evaluation files.
Saves results to group_stats.json for later HTML generation.
"""

import subprocess
import re
import time
import json
from pathlib import Path
from collections import defaultdict


def get_group_order_from_smallgroups():
    """Parse SmallGroups.lean to get ordered list of (order, gap_id) tuples."""
    smallgroups_file = Path("Playground/Geometry/SmallGroups/SmallGroups.lean")
    groups = []

    with open(smallgroups_file, 'r') as f:
        for line in f:
            line = line.strip()
            # Skip comments, imports, and options
            if line.startswith('--') or line.startswith('import') or line.startswith('set_option') or not line:
                continue
            # Match abbrev statements: abbrev Gap_N_M := ...
            match = re.match(r'abbrev\s+Gap_(\d+)_(\d+)\s+:=', line)
            if match:
                order = int(match.group(1))
                gap_id = int(match.group(2))
                groups.append((order, gap_id))

    return groups


def run_build():
    """Run lake build for all eval files and capture outputs."""
    eval_files = [
        ("Playground.Geometry.SmallGroups.EvalCardinality", "cardinality"),
        ("Playground.Geometry.SmallGroups.EvalAbelian", "abelian"),
        ("Playground.Geometry.SmallGroups.EvalFracInvolutions", "fracinvolutions"),
        ("Playground.Geometry.SmallGroups.EvalCommutingFraction", "commutingfraction"),
        ("Playground.Geometry.SmallGroups.EvalNumSubgroups", "numsubgroups"),
        ("Playground.Geometry.SmallGroups.EvalExponent", "exponent"),
    ]

    outputs = {}
    for eval_file, property_name in eval_files:
        print(f"Building {eval_file}...")

        # Use Popen to stream output while also capturing it
        process = subprocess.Popen(
            ["lake", "build", eval_file],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1
        )

        # Stream output line by line while collecting it
        collected_output = []
        for line in process.stdout:
            print(line, end='')  # Print to stdout in real-time
            collected_output.append(line)

        process.wait()
        outputs[property_name] = ''.join(collected_output)

    return outputs


def parse_output(outputs):
    """Parse the build outputs from all eval files to extract group information."""
    groups = defaultdict(dict)

    # Get ordered list of groups from SmallGroups.lean
    group_order = get_group_order_from_smallgroups()

    # Property name mapping to dict keys
    property_map = {
        'Cardinality': 'card',
        'Abelian': 'abelian',
        'FracInvolutions': 'frac_involutions',
        'CommutingFraction': 'commuting_fraction',
        'NumSubgroups': 'num_subgroups',
        'Exponent': 'exponent',
    }

    # Parse each property's output
    for property_name, output in outputs.items():
        # Look for the info line with the array output
        # Pattern: info: Playground/Geometry/SmallGroups/EvalCardinality.lean:5:0: [1, 2, 3, ...]
        pattern = r'info: Playground/Geometry/SmallGroups/Eval(\w+)\.lean:\d+:\d+: \[(.+?)\]'

        # Try to match single-line array first
        match = re.search(pattern, output, re.DOTALL)
        if match:
            eval_type = match.group(1)  # e.g., "Cardinality"
            array_content = match.group(2).strip()

            # Split by comma, but be careful with nested structures like "mkRat 1 3"
            # Simple split works for most cases
            values = [v.strip() for v in array_content.split(',')]

            # Map each value to the corresponding group
            dict_key = property_map.get(eval_type, eval_type.lower())
            for i, value in enumerate(values):
                if i < len(group_order):
                    key = group_order[i]
                    groups[key][dict_key] = value

    return groups


def parse_lean_files():
    """Parse SmallGroups.lean to extract group names and abbrev definitions."""
    smallgroups_file = Path("Playground/Geometry/SmallGroups/SmallGroups.lean")
    group_info = {}

    with open(smallgroups_file, 'r') as f:
        for line in f:
            line = line.strip()
            # Skip comments, imports, and options
            if line.startswith('--') or line.startswith('import') or line.startswith('set_option') or not line:
                continue
            # Match abbrev statements: abbrev Gap_N_M := definition
            match = re.match(r'abbrev\s+(Gap_(\d+)_(\d+))\s*:=\s*(.+?)(?=\n|$)', line)
            if match:
                abbrev_name = match.group(1)
                order = int(match.group(2))
                gap_id = int(match.group(3))
                abbrev_def = match.group(4).strip()
                group_info[(order, gap_id)] = {
                    'name': abbrev_name,
                    'definition': abbrev_def
                }

    return group_info


def save_stats(groups, group_info, output_file="group_stats.json"):
    """Save collected stats to JSON file."""
    # Convert tuple keys to strings for JSON serialization
    stats = {
        'groups': {f"{order},{gap_id}": data for (order, gap_id), data in groups.items()},
        'group_info': {f"{order},{gap_id}": info for (order, gap_id), info in group_info.items()}
    }

    with open(output_file, 'w') as f:
        json.dump(stats, f, indent=2)

    return output_file


def main():
    """Main function."""
    print("Parsing Lean files for group names and definitions...")
    group_info = parse_lean_files()
    print(f"Found {len(group_info)} group definitions from Lean files")

    # Run build and capture outputs
    build_start = time.time()
    outputs = run_build()
    build_time = time.time() - build_start
    print(f"Lake build completed in {build_time:.2f}s")

    # Parse the outputs
    groups = parse_output(outputs)
    print(f"Found {len(groups)} groups from build output")

    # Save to JSON
    output_file = save_stats(groups, group_info)
    print(f"Statistics saved to {output_file}")


if __name__ == "__main__":
    main()
