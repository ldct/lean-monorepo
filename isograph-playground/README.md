# IsoGraph playground

A small Lean project for experimenting with
[IsoGraph](https://github.com/Timeroot/IsoGraph), a finite graph theory library
whose graphs are considered up to isomorphism.

The project uses Lean 4.33.1 to match IsoGraph. Fetch the dependencies and build
the example with:

```sh
lake update
lake env lake build
```

IsoGraph enables precompiled modules. On Linux, `lake env lake build` ensures
that the Lean shared libraries are available while its dependencies build.
