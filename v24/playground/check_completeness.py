#!/usr/bin/env python3
"""
Check that all Gap group files are complete.

A complete file should have:
1. import Mathlib
2. import Playground.Geometry.SmallGroups.GroupProps
3. An abbrev for the group

Note: #eval blocks are now centralized in separate evaluation files.
"""

import re
from pathlib import Path
from dataclasses import dataclass
from typing import List, Optional


@dataclass
class FileCheck:
    """Result of checking a file."""
    file_path: Path
    has_mathlib_import: bool
    has_groupprops_import: bool
    has_abbrev: bool
    abbrev_name: Optional[str] = None

    @property
    def is_complete(self) -> bool:
        """Check if the file is complete."""
        return all([
            self.has_mathlib_import,
            self.has_groupprops_import,
            self.has_abbrev,
        ])

    @property
    def missing_items(self) -> List[str]:
        """Get list of missing items."""
        missing = []
        if not self.has_mathlib_import:
            missing.append("import Mathlib")
        if not self.has_groupprops_import:
            missing.append("import Playground.Geometry.SmallGroups.GroupProps")
        if not self.has_abbrev:
            missing.append("abbrev declaration")
        return missing


def check_file(file_path: Path) -> FileCheck:
    """Check if a file is complete."""
    content = file_path.read_text()
    lines = content.split('\n')

    # Check for imports
    has_mathlib_import = any('import Mathlib' in line for line in lines)
    has_groupprops_import = any('import Playground.Geometry.SmallGroups.GroupProps' in line for line in lines)

    # Check for abbrev and extract name
    has_abbrev = False
    abbrev_name = None
    for line in lines:
        abbrev_match = re.match(r'abbrev\s+(\w+)\s*:=', line)
        if abbrev_match:
            has_abbrev = True
            abbrev_name = abbrev_match.group(1)
            break

    return FileCheck(
        file_path=file_path,
        has_mathlib_import=has_mathlib_import,
        has_groupprops_import=has_groupprops_import,
        has_abbrev=has_abbrev,
        abbrev_name=abbrev_name,
    )


def main():
    """Main function."""
    # Find all Gap_*.lean files
    smallgroups_dir = Path("Playground/Geometry/SmallGroups")
    gap_files = sorted(smallgroups_dir.glob("Gap_*/Gap_*.lean"))

    if not gap_files:
        print("No Gap files found!")
        return

    print(f"Checking {len(gap_files)} files...\n")

    incomplete_files = []
    complete_files = []

    for file_path in gap_files:
        check = check_file(file_path)
        if check.is_complete:
            complete_files.append(check)
        else:
            incomplete_files.append(check)

    # Print results
    if complete_files:
        print(f"✓ {len(complete_files)} complete files:")
        for check in complete_files:
            print(f"  ✓ {check.file_path.parent.name}/{check.file_path.name}")

    if incomplete_files:
        print(f"\n✗ {len(incomplete_files)} incomplete files:\n")
        for check in incomplete_files:
            print(f"  ✗ {check.file_path.parent.name}/{check.file_path.name}")
            if check.abbrev_name:
                print(f"     Group: {check.abbrev_name}")
            print(f"     Missing:")
            for item in check.missing_items:
                print(f"       - {item}")
            print()

    # Summary
    print("=" * 60)
    print(f"Summary: {len(complete_files)} complete, {len(incomplete_files)} incomplete")

    # Exit with error code if there are incomplete files
    if incomplete_files:
        exit(1)


if __name__ == "__main__":
    main()
