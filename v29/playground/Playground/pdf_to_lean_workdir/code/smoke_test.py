#!/usr/bin/env python3
"""
Smoke test: validates scaffolding, extraction, prompt loading, and agent connectivity
without running the full formalization loop (which is expensive).
"""

import argparse
import asyncio
import glob
import os
import re
import subprocess
import sys

import yaml

# Add this directory to path so scaffold/validate can be imported
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from scaffold import scaffold
from pipeline import discover_chapters, load_prompt, make_claude_options
from agent_framework.anthropic import ClaudeAgent


async def main():
    parser = argparse.ArgumentParser(description="Smoke test for the formalization pipeline")
    parser.add_argument("input_dir", help="Directory containing ch*.txt input files")
    parser.add_argument("output_dir", help="Directory for smoke test output")
    args = parser.parse_args()

    script_dir = os.path.dirname(os.path.abspath(__file__))
    project_base = os.path.dirname(script_dir)  # formalization_upgrade/
    input_dir = os.path.abspath(args.input_dir)
    output_dir = os.path.abspath(args.output_dir)
    config_path = os.path.join(project_base, "config.yaml")
    prompts_dir = os.path.join(project_base, "prompts")
    evaluation_dir = os.path.join(project_base, "evaluation")

    with open(config_path) as f:
        config = yaml.safe_load(f)

    claude_cfg = config.get("claude", {})

    passed = 0
    failed = 0

    def check(name: str, condition: bool, detail: str = ""):
        nonlocal passed, failed
        if condition:
            print(f"  PASS: {name}")
            passed += 1
        else:
            print(f"  FAIL: {name} -- {detail}")
            failed += 1

    # -------------------------------------------------------
    # Test 1: Discover chapters
    # -------------------------------------------------------
    print("\n=== Test 1: Discover chapters ===")
    chapters = discover_chapters(input_dir)
    check("Found chapters", len(chapters) > 0, f"No ch*.txt in {input_dir}")
    print(f"  Discovered chapters: {chapters}")

    # -------------------------------------------------------
    # Test 2: Scaffold
    # -------------------------------------------------------
    print("\n=== Test 2: Scaffold project ===")
    scaffold(input_dir, output_dir, chapters)
    check("lakefile.toml exists", os.path.exists(os.path.join(output_dir, "lakefile.toml")))
    check("lean-toolchain exists", os.path.exists(os.path.join(output_dir, "lean-toolchain")))
    check("Formalization.lean exists", os.path.exists(os.path.join(output_dir, "Formalization.lean")))
    for ch in chapters:
        check(f"ch{ch}.lean placeholder exists", os.path.exists(os.path.join(output_dir, "Formalization", f"ch{ch}.lean")))
    check("raw data copied", os.path.exists(os.path.join(output_dir, "natural_language", "raw_data", f"ch{chapters[0]}.txt")))

    # Check Formalization.lean content
    with open(os.path.join(output_dir, "Formalization.lean")) as f:
        root_content = f.read()
    for ch in chapters:
        check(f"Root import has ch{ch}", f"import Formalization.ch{ch}" in root_content)

    # -------------------------------------------------------
    # Test 3: Extract theorems
    # -------------------------------------------------------
    print("\n=== Test 3: Extract theorem blocks ===")
    theorems_dir = os.path.join(output_dir, "natural_language", "raw_data", "theorems_and_defs")
    extract_script = os.path.join(evaluation_dir, "keep_only_theorems_and_defs.py")
    for ch in chapters:
        src = os.path.join(input_dir, f"ch{ch}.txt")
        dst = os.path.join(theorems_dir, f"ch{ch}.txt")
        subprocess.run([sys.executable, extract_script, src, dst], check=True, capture_output=True)
        check(f"ch{ch} theorems extracted", os.path.exists(dst))

    first_ch = chapters[0]
    with open(os.path.join(theorems_dir, f"ch{first_ch}.txt")) as f:
        first_theorems = f.read()
    has_theorems = "\\begin{theorem}" in first_theorems or "\\begin{definition}" in first_theorems or "\\begin{lemma}" in first_theorems
    check(f"ch{first_ch} has theorem/def blocks", has_theorems, "No theorem/definition blocks found")

    # -------------------------------------------------------
    # Test 4: Prompt loading
    # -------------------------------------------------------
    print("\n=== Test 4: Prompt loading ===")
    prompt_files = ["statement_fl.md", "statement_verify.md", "verdict_statement.md",
                    "proof_search.md", "proof_verify.md", "verdict_proof.md", "check_statement_change.md"]
    for pf in prompt_files:
        exists = os.path.exists(os.path.join(prompts_dir, pf))
        check(f"Prompt {pf} exists", exists)

    # Try loading a prompt with variable substitution
    try:
        prompt = load_prompt(
            prompts_dir, "statement_fl.md",
            ch_num=first_ch,
            raw_data_dir=os.path.join(output_dir, "natural_language", "raw_data"),
            theorems_and_defs_dir=theorems_dir,
            lean_chapter_file=os.path.join(output_dir, "Formalization", f"ch{first_ch}.lean"),
            lean_src_dir=os.path.join(output_dir, "Formalization"),
            project_root=output_dir,
            evaluation_dir=evaluation_dir,
            reuse_instructions="This is the first chapter.",
            status_file="/tmp/test_status.md",
        )
        check("statement_fl.md renders OK", f"ch{first_ch}" in prompt)
        check("No unresolved placeholders", "{ch_num}" not in prompt, "Found unresolved {ch_num}")
    except Exception as e:
        check("statement_fl.md renders OK", False, str(e))

    # -------------------------------------------------------
    # Test 5: ClaudeAgent connectivity
    # -------------------------------------------------------
    print("\n=== Test 5: ClaudeAgent connectivity ===")
    claude_opts = make_claude_options(claude_cfg, output_dir)
    try:
        async with ClaudeAgent(default_options=claude_opts) as agent:
            response = await agent.run("Reply with exactly: SMOKE_TEST_OK")
            text = response.text or ""
            check("Agent responds", len(text) > 0, "Empty response")
            check("Agent response contains expected text", "SMOKE_TEST_OK" in text.upper() or "smoke" in text.lower(),
                  f"Got: {text[:100]}")
    except Exception as e:
        check("Agent connectivity", False, str(e))

    # -------------------------------------------------------
    # Summary
    # -------------------------------------------------------
    print(f"\n{'=' * 60}")
    print(f"SMOKE TEST RESULTS: {passed} passed, {failed} failed")
    print(f"{'=' * 60}")

    if failed > 0:
        sys.exit(1)


if __name__ == "__main__":
    asyncio.run(main())
