#!/usr/bin/env python3
"""
Collect group statistics by building and running evaluation files.
First runs lake build on all targets, then runs lake exe to collect data.
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
    """Build all targets, then run lake exe for all eval files and capture outputs."""
    eval_files = [
        ("Playground.Geometry.SmallGroups.EvalCardinality", "cardinality"),
        ("Playground.Geometry.SmallGroups.EvalAbelian", "abelian"),
        ("Playground.Geometry.SmallGroups.EvalFracInvolutions", "fracinvolutions"),
        ("Playground.Geometry.SmallGroups.EvalCommutingFraction", "commutingfraction"),
        ("Playground.Geometry.SmallGroups.EvalNumSubgroups", "numsubgroups"),
        ("Playground.Geometry.SmallGroups.EvalZ1Size", "z1size"),
        ("Playground.Geometry.SmallGroups.EvalZ2Size", "z2size"),
        ("Playground.Geometry.SmallGroups.EvalZ3Size", "z3size"),
        ("Playground.Geometry.SmallGroups.EvalZ4Size", "z4size"),
        ("Playground.Geometry.SmallGroups.EvalExponent", "exponent"),
    ]

    # First, build all targets
    print("Building all targets...")
    build_start = time.time()
    build_times = {}
    for eval_file, property_name in eval_files:
        print(f"  Building {eval_file}...")
        file_build_start = time.time()
        process = subprocess.Popen(
            ["lake", "build", eval_file],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1
        )
        stdout, stderr = process.communicate()

        # Print build output
        if stderr:
            print(stderr, end='')
        if stdout:
            print(stdout, end='')

        file_build_time = time.time() - file_build_start
        build_times[property_name] = file_build_time
        print(f"  {property_name} build took {file_build_time:.2f}s")

    build_time = time.time() - build_start
    print(f"Build completed in {build_time:.2f}s\n")

    # Then, run all executables
    print("Running executables...")
    run_start = time.time()
    outputs = {}
    run_times = {}
    for eval_file, property_name in eval_files:
        print(f"  Running {eval_file}...")
        file_run_start = time.time()

        # Use Popen to capture stdout and stderr separately
        process = subprocess.Popen(
            ["lake", "exe", eval_file],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1
        )

        # Wait for process to complete and get outputs
        stdout, stderr = process.communicate()

        # Print stderr (build progress) to console
        if stderr:
            print(stderr, end='')

        # Print stdout (actual data) to console
        if stdout:
            print(stdout, end='')

        # Store only stdout for parsing
        outputs[property_name] = stdout

        file_run_time = time.time() - file_run_start
        run_times[property_name] = file_run_time
        print(f"  {property_name} execution took {file_run_time:.2f}s")

    run_time = time.time() - run_start
    print(f"Execution completed in {run_time:.2f}s")

    return outputs, build_time, run_time, build_times, run_times


def parse_output(outputs):
    """Parse the exe outputs from all eval files to extract group information."""
    groups = defaultdict(dict)

    # Get ordered list of groups from SmallGroups.lean
    group_order = get_group_order_from_smallgroups()

    # Property name mapping to dict keys
    property_map = {
        'cardinality': 'card',
        'abelian': 'abelian',
        'fracinvolutions': 'frac_involutions',
        'commutingfraction': 'commuting_fraction',
        'numsubgroups': 'num_subgroups',
        'exponent': 'exponent',
    }

    # Parse each property's output
    for property_name, output in outputs.items():
        # Look for the array output directly (format: [1, 2, 3, ...])
        # Use a pattern that matches arrays with proper content (numbers, booleans, or Rat values)
        pattern = r'\[([\d\s,()true|false:Rat/]+)\]'

        # Try to match the array
        match = re.search(pattern, output, re.DOTALL)
        if match:
            array_content = match.group(1).strip()

            # Split by comma, but be careful with nested structures like "mkRat 1 3"
            # Simple split works for most cases
            values = [v.strip() for v in array_content.split(',')]

            # Map each value to the corresponding group
            dict_key = property_map.get(property_name, property_name.lower())
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
        json.dump(stats, f, indent=2, sort_keys=True)

    return output_file


def main():
    """Main function."""
    print("Parsing Lean files for group names and definitions...")
    group_info = parse_lean_files()
    print(f"Found {len(group_info)} group definitions from Lean files")

    # Build and run executables, capture outputs
    outputs, build_time, run_time, build_times, run_times = run_build()

    print(f"\nTiming summary:")
    print(f"  Build time: {build_time:.2f}s")
    print(f"  Run time: {run_time:.2f}s")
    print(f"  Total time: {build_time + run_time:.2f}s")

    print(f"\nPer-file timing:")
    for name in sorted(build_times.keys()):
        print(f"  {name}: build={build_times[name]:.2f}s, run={run_times[name]:.2f}s, total={build_times[name] + run_times[name]:.2f}s")

    # Parse the outputs
    groups = parse_output(outputs)
    print(f"\nFound {len(groups)} groups from execution output")

    # Save to JSON
    output_file = save_stats(groups, group_info)
    print(f"Statistics saved to {output_file}")


if __name__ == "__main__":
    main()
