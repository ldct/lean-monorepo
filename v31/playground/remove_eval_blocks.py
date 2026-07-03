#!/usr/bin/env python3
"""
Remove #eval blocks from all group files in SmallGroups project.
"""

import re
from pathlib import Path

def parse_smallgroups_imports():
    """Parse SmallGroups.lean to get list of all group import paths."""
    smallgroups_file = Path("Playground/Geometry/SmallGroups/SmallGroups.lean")
    imports = []

    with open(smallgroups_file, 'r') as f:
        for line in f:
            line = line.strip()
            # Skip commented imports
            if line.startswith('--'):
                continue
            # Match import statements
            match = re.match(r'import (Playground\.Geometry\.SmallGroups\.Gap_\d+\.Gap_\d+_\d+)', line)
            if match:
                imports.append(match.group(1))

    return imports

def import_to_filepath(import_path):
    """Convert import path to file path."""
    return import_path.replace('.', '/') + '.lean'

def remove_eval_blocks(filepath):
    """Remove #eval blocks from a group file, keeping only imports and abbrev."""
    with open(filepath, 'r') as f:
        lines = f.readlines()

    # Keep only non-#eval lines
    filtered_lines = []
    for line in lines:
        stripped = line.strip()
        if not stripped.startswith('#eval'):
            filtered_lines.append(line)

    # Write back to file
    with open(filepath, 'w') as f:
        f.writelines(filtered_lines)

    return len(lines) - len(filtered_lines)

def main():
    """Main function to remove #eval blocks from all group files."""
    imports = parse_smallgroups_imports()
    print(f"Found {len(imports)} group files to process\n")

    total_removed = 0
    for import_path in imports:
        filepath = import_to_filepath(import_path)
        removed = remove_eval_blocks(filepath)
        if removed > 0:
            print(f"  {filepath}: removed {removed} #eval lines")
            total_removed += removed

    print(f"\n✅ Removed {total_removed} #eval lines from {len(imports)} files")

if __name__ == "__main__":
    main()
