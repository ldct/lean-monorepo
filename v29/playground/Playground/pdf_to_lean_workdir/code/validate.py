"""Stage 4: Final validation of the entire project."""

import os
import re
import subprocess
import sys
from datetime import datetime


def count_theorems(content: str) -> int:
    return len(re.findall(r'^(?:theorem|lemma)\s+Ch\d+_', content, re.MULTILINE))


def count_defs(content: str) -> int:
    return len(re.findall(r'^def\s+', content, re.MULTILINE))


def validate(project_root: str, chapters: list[int], evaluation_dir: str) -> bool:
    """Run final validation. Returns True if all pass."""
    all_pass = True
    report_lines = []

    def report(line=""):
        report_lines.append(line)
        print(line)

    report("# Formalization Summary Report")
    report()
    report(f"**Generated:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    report(f"**Project:** `{project_root}`")
    report(f"**Chapters:** {len(chapters)} ({', '.join(str(c) for c in chapters)})")
    report()

    # 1. Full project build
    report("---")
    report()
    report("## 1. Build Verification")
    report()
    build_result = subprocess.run(
        ["lake", "build"], cwd=project_root, capture_output=True, text=True
    )
    if build_result.returncode != 0:
        report("**Status:** FAIL")
        report()
        report("```")
        report(build_result.stderr.strip())
        report("```")
        all_pass = False
    else:
        report("**Status:** PASS")
    report()

    # 2. Per-chapter checks
    report("---")
    report()
    report("## 2. Per-Chapter Results")
    report()

    total_theorems = 0
    total_defs = 0
    total_lines = 0

    for ch in chapters:
        lean_file = os.path.join(project_root, "Formalization", f"ch{ch}.lean")
        specs_file = os.path.join(project_root, "Formalization", "intermediate_files", f"ch{ch}", f"ch{ch}_specs.lean")
        theorems_file = os.path.join(project_root, "natural_language", "raw_data", "theorems_and_defs", f"ch{ch}.txt")

        ch_pass = True

        report(f"### Chapter {ch}")
        report()

        if not os.path.exists(lean_file):
            report(f"**Status:** FAIL -- `ch{ch}.lean` does not exist")
            report()
            all_pass = False
            continue

        with open(lean_file) as f:
            content = f.read()

        line_count = content.count("\n") + 1
        theorem_count = count_theorems(content)
        def_count = count_defs(content)
        sorry_count = len(re.findall(r'\bsorry\b', content))
        axiom_count = len(re.findall(r'^\s*axiom\s+', content, re.MULTILINE))

        total_theorems += theorem_count
        total_defs += def_count
        total_lines += line_count

        if sorry_count > 0:
            ch_pass = False
            all_pass = False
        if axiom_count > 0:
            ch_pass = False
            all_pass = False

        # Lean statement coverage check (specs preserved)
        coverage_status = "N/A"
        if os.path.exists(specs_file):
            cov_script = os.path.join(evaluation_dir, "check_coverage_lean_statement.py")
            cov_result = subprocess.run(
                [sys.executable, cov_script, specs_file, lean_file],
                capture_output=True, text=True,
            )
            coverage_status = "PASS" if cov_result.returncode == 0 else "FAIL"
            if cov_result.returncode != 0:
                ch_pass = False
                all_pass = False
        else:
            coverage_status = "SKIP (no specs file)"

        # LaTeX quote coverage check (all theorem blocks present)
        latex_coverage_status = "N/A"
        if os.path.exists(theorems_file):
            latex_cov_script = os.path.join(evaluation_dir, "check_coverage_latex_quote.py")
            latex_cov_result = subprocess.run(
                [sys.executable, latex_cov_script, theorems_file, lean_file],
                capture_output=True, text=True,
            )
            latex_coverage_status = "PASS" if latex_cov_result.returncode == 0 else "FAIL"
            if latex_cov_result.returncode != 0:
                ch_pass = False
                all_pass = False
        else:
            latex_coverage_status = "SKIP (no theorems file)"

        overall = "PASS" if ch_pass else "FAIL"

        report(f"| Check | Status |")
        report(f"|-------|--------|")
        report(f"| Sorry-free | {'PASS' if sorry_count == 0 else 'FAIL'} ({sorry_count} found) |")
        report(f"| Axiom-free | {'PASS' if axiom_count == 0 else 'FAIL'} ({axiom_count} found) |")
        report(f"| Lean statement coverage | {coverage_status} |")
        report(f"| LaTeX quote coverage | {latex_coverage_status} |")
        report(f"| **Overall** | **{overall}** |")
        report()
        report(f"| Metric | Value |")
        report(f"|--------|-------|")
        report(f"| Theorems | {theorem_count} |")
        report(f"| Definitions | {def_count} |")
        report(f"| Lines | {line_count} |")
        report()

    # 3. Overall summary
    report("---")
    report()
    report("## 3. Overall Summary")
    report()
    report(f"| Metric | Value |")
    report(f"|--------|-------|")
    report(f"| Chapters | {len(chapters)} |")
    report(f"| Total theorems | {total_theorems} |")
    report(f"| Total definitions | {total_defs} |")
    report(f"| Total lines | {total_lines} |")
    report(f"| Build | {'PASS' if build_result.returncode == 0 else 'FAIL'} |")
    report(f"| **Final verdict** | **{'ALL PASS' if all_pass else 'SOME CHECKS FAILED'}** |")
    report()

    # Write report
    report_path = os.path.join(project_root, "final_summary.md")
    with open(report_path, "w") as f:
        f.write("\n".join(report_lines) + "\n")

    print(f"\nReport written to: {report_path}")
    return all_pass
