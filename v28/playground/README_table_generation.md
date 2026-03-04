# Group Table Generation

The HTML table generation is split into two separate scripts for efficiency:

## Two-Step Process

### Step 1: Collect Statistics (`collect_group_stats.py`)

Runs Lean builds to compute group properties and saves results to JSON.

```bash
python3 collect_group_stats.py
```

**What it does:**
- Parses all Lean group files to extract definitions
- Runs `lake build` on 5 evaluation files:
  - EvalCardinality
  - EvalAbelian
  - EvalFracInvolutions
  - EvalCommutingFraction
  - EvalNumSubgroups
- Parses build output to extract computed properties
- Saves everything to `group_stats.json`

**Time:** ~55 seconds (depends on build cache)

**Output:** `group_stats.json` (56KB)

### Step 2: Generate HTML (`generate_groups_table_from_json.py`)

Reads stats from JSON and generates the HTML table.

```bash
python3 generate_groups_table_from_json.py
```

**What it does:**
- Loads all groups from `group_names.tsv`
- Loads computed statistics from `group_stats.json`
- Combines implemented + unimplemented groups
- Generates HTML with proper formatting

**Time:** ~0.1 seconds

**Output:** `groups_table.html` (204KB)

## Workflow

**Full rebuild (after changing group definitions):**
```bash
python3 collect_group_stats.py
python3 generate_groups_table_from_json.py
```

**Quick HTML regeneration (after changing formatting/display):**
```bash
python3 generate_groups_table_from_json.py
```

## Benefits of Split Approach

1. **Fast iteration on HTML design** - Regenerate table in 0.1s vs 55s
2. **Reusable stats** - JSON can be used for other analyses
3. **Clear separation** - Computation vs presentation
4. **Debugging** - Can inspect `group_stats.json` directly

## File Overview

| File | Purpose | Runtime | Output |
|------|---------|---------|--------|
| `collect_group_stats.py` | Run Lean builds, collect stats | ~55s | `group_stats.json` |
| `generate_groups_table_from_json.py` | Generate HTML from JSON | ~0.1s | `groups_table.html` |
| `group_stats.json` | Cached statistics | - | 56KB JSON |
| `group_names.tsv` | All groups (from website) | - | 311 groups |
| `groups_table.html` | Final output | - | 204KB HTML |

## Legacy Script

`generate_groups_table.py` - Original monolithic script (still works but slower for iteration)

## Example Output

The HTML table shows:
- **199/311 groups (64.0%)** implemented
- **38/60 complete orders**
- Implemented groups: full stats (abelian, fractions, subgroups)
- Unimplemented groups: label from TSV, stats show "-"
