#!/usr/bin/env -S uv run -s
# /// script
# requires-python = ">=3.11"
# dependencies = [
#   "aristotlelib",
# ]
# ///

import asyncio
import aristotlelib

async def main():
    # Prove a theorem from a Lean file
    solution_path = await aristotlelib.Project.prove_from_file("Playground/AristotleTest.lean")
    print(f"Solution saved to: {solution_path}")

asyncio.run(main())