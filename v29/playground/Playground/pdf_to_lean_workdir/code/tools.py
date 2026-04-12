"""Custom tools for the formalization pipeline agents."""

import json
import urllib.parse
import urllib.request
from agent_framework import tool


@tool(name="loogle_search", description="""Search Mathlib4 lemmas by type pattern using Loogle (https://loogle.lean-lang.org).

Use this when you need to find the correct Mathlib lemma name, or discover what lemmas exist for a given type signature.

## Query syntax (combine multiple filters with commas):

1. **By constant name**: `Real.sin` — finds lemmas mentioning a specific constant
2. **By name substring**: `"differ"` — finds lemmas with "differ" in the name
3. **By subexpression**: `_ * (_ ^ _)` — pattern matching on statement structure. Use `_` as wildcard.
4. **By conclusion**: `|- tsum _ = _ * tsum _` — match the conclusion (after `|-`)
5. **By hypothesis pattern**: `_ → _ → tsum _ < tsum _` — match hypothesis shapes
6. **Combined**: `IsCompact, IsClosed` — multiple filters, returns lemmas matching ALL

## Examples:

- `loogle_search("IsCompact, IsClosed")` → finds `IsCompact.of_isClosed_subset`, `IsClosed.isCompact`, etc.
- `loogle_search("List.length, _ ++ _")` → finds lemmas about length of appended lists
- `loogle_search("|- _ < _ → tsum _ < tsum _")` → finds lemmas where conclusion matches this pattern
- `loogle_search("Finset.sum, _ * _")` → finds lemmas about sums involving multiplication
- `loogle_search('"decidable", Prop')` → finds decidability lemmas for Prop

## Tips:

- Use this when `exact?` or `apply?` in Lean are too slow or don't find what you need
- If you get too many results, add more filters
- If you get no results, try relaxing the pattern (use more `_` wildcards)
- The `name` field in results is the exact Lean identifier you can use in your proof
- The `module` field tells you which import you need
""")
def loogle_search(query: str) -> str:
    """Search Mathlib4 lemmas by type pattern using the Loogle API."""
    encoded = urllib.parse.quote(query)
    url = f"https://loogle.lean-lang.org/json?q={encoded}"

    try:
        req = urllib.request.Request(url, headers={"User-Agent": "formalization-pipeline/1.0"})
        with urllib.request.urlopen(req, timeout=30) as resp:
            data = json.loads(resp.read())
    except Exception as e:
        return f"Loogle API error: {e}"

    count = data.get("count", 0)
    header = data.get("header", "")
    hits = data.get("hits", [])
    error = data.get("error", None)

    if error:
        return f"Loogle error: {error}\n\nSuggestions: {data.get('suggestions', [])}"

    if count == 0:
        return "No results found. Try relaxing the query (use more _ wildcards or fewer filters)."

    # Format top results (max 15 to keep output manageable)
    lines = [header, ""]
    for h in hits[:15]:
        name = h.get("name", "?")
        typ = h.get("type", "?")
        module = h.get("module", "?")
        doc = h.get("doc", "")
        lines.append(f"• {name}")
        lines.append(f"  Type: {typ}")
        lines.append(f"  Module: {module}")
        if doc:
            # Show first line of doc only
            first_doc_line = doc.strip().split("\n")[0][:120]
            lines.append(f"  Doc: {first_doc_line}")
        lines.append("")

    if count > 15:
        lines.append(f"... and {count - 15} more results. Refine your query for fewer results.")

    return "\n".join(lines)
