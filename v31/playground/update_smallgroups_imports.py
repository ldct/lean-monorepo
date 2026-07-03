#!/usr/bin/env python3
"""
Update SmallGroups.lean with all group imports, sorted by order and gap_id.
"""

import re
from pathlib import Path

def get_all_group_files():
    """Get all Gap_*.lean files."""
    base_dir = Path("Playground/Geometry/SmallGroups")
    files = []

    for gap_file in base_dir.glob("Gap_*/Gap_*.lean"):
        # Extract order and gap_id from filename
        parts = gap_file.stem.split("_")
        if len(parts) >= 3:
            try:
                order = int(parts[1])
                gap_id = int(parts[2])
                files.append((order, gap_id, gap_file))
            except ValueError:
                continue

    return sorted(files)

def generate_import_line(gap_file):
    """Generate import line from file path."""
    # Convert path to module path
    # Playground/Geometry/SmallGroups/Gap_16/Gap_16_11.lean
    # -> import Playground.Geometry.SmallGroups.Gap_16.Gap_16_11
    parts = gap_file.parts
    module_parts = parts[:-1] + (gap_file.stem,)
    return f"import {'.'.join(module_parts)}"

def main():
    """Main function."""
    files = get_all_group_files()
    print(f"Found {len(files)} group files")

    # Generate import lines
    import_lines = []
    for order, gap_id, gap_file in files:
        import_line = generate_import_line(gap_file)
        import_lines.append(import_line)

    # Write to SmallGroups.lean
    output_file = Path("Playground/Geometry/SmallGroups/SmallGroups.lean")
    content = "\n".join(import_lines) + "\n"
    output_file.write_text(content)

    print(f"✅ Updated {output_file} with {len(import_lines)} imports")

if __name__ == "__main__":
    main()
