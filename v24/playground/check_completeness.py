#!/usr/bin/env python3
"""
Check that all Gap group files are complete.

A complete file should have:
1. import Mathlib
2. import Playground.Geometry.SmallGroups.GroupProps
3. An abbrev for the group
4. #eval Fintype.card
5. #eval Group.IsAbelian
6. #eval Group.FracInvolutions
7. #eval Group.CommutingFraction
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
    has_card_eval: bool
    has_abelian_eval: bool
    has_frac_involutions_eval: bool
    has_commuting_fraction_eval: bool
    abbrev_name: Optional[str] = None

    @property
    def is_complete(self) -> bool:
        """Check if the file is complete."""
        return all([
            self.has_mathlib_import,
            self.has_groupprops_import,
            self.has_abbrev,
            self.has_card_eval,
            self.has_abelian_eval,
            self.has_frac_involutions_eval,
            self.has_commuting_fraction_eval,
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
        if not self.has_card_eval:
            missing.append("#eval Fintype.card")
        if not self.has_abelian_eval:
            missing.append("#eval Group.IsAbelian")
        if not self.has_frac_involutions_eval:
            missing.append("#eval Group.FracInvolutions")
        if not self.has_commuting_fraction_eval:
            missing.append("#eval Group.CommutingFraction")
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

    # Check for #eval statements
    has_card_eval = any('#eval Fintype.card' in line for line in lines)
    has_abelian_eval = any('#eval Group.IsAbelian' in line for line in lines)
    has_frac_involutions_eval = any('#eval Group.FracInvolutions' in line for line in lines)
    has_commuting_fraction_eval = any('#eval Group.CommutingFraction' in line for line in lines)

    return FileCheck(
        file_path=file_path,
        has_mathlib_import=has_mathlib_import,
        has_groupprops_import=has_groupprops_import,
        has_abbrev=has_abbrev,
        has_card_eval=has_card_eval,
        has_abelian_eval=has_abelian_eval,
        has_frac_involutions_eval=has_frac_involutions_eval,
        has_commuting_fraction_eval=has_commuting_fraction_eval,
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
