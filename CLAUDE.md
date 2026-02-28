# lean-monorepo

## How to search for theorems

When looking for Mathlib theorem names, use these search APIs. Prefer leanexplore; fall back to leansearch if leanexplore is down.

### leanexplore (preferred)

```
curl 'https://www.leanexplore.com/api/search?q=<query>&pkg=Init&pkg=Batteries&pkg=Std&pkg=Mathlib'
```

### leansearch (fallback)

```
curl -X POST 'https://leansearch.net/search' \
  -H 'Content-Type: application/json' \
  -d '{"query":["<natural language query>"],"num_results":10}'
```

Results include `result.name`, `result.signature`, `result.module_name`, and `result.kind`.
