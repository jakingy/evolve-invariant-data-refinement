# GitHub Pages source browser

Build with Python 3.10 or later:

```
python -m pip install -r site/requirements.txt
python site/build.py
python site/check.py
python -m http.server 8000 --directory _site
```

The site reads only the files in `manifest.json`: it does not publish the full
upstream theories. All proofs and comments in the exported sources remain visible.
Highlighting is lexical, not the semantic colouring of Isabelle/PIDE.

`symbols.json` contains the Unicode mappings from Isabelle2025-2 `etc/symbols`,
overridden by the five project symbols in `new_rg_algebra/symbols`. In particular,
weak conjunction renders as ⋒. Isabelle fonts and their distribution notices are
included in `assets/` so the browser does not depend on installed system fonts.

To publish, push these files and select **Settings → Pages → Build and deployment
→ Source: GitHub Actions** in the repository. The workflow builds and deploys the
site on pushes to main. No Isabelle proof build is required for presentation.

Expected homepage:
`https://jakingy.github.io/evolve-invariant-data-refinement/`

Declaration links use the existing manifest identifier, for example:
`theories/Commands/Bind.thy.html#isa:Commands-Bind-bind-rely-alt`.
Line links such as `#L42` are also supported. Prefer declaration identifiers in
the thesis, since they remain stable if lines are inserted above the declaration.
Raw exported theories are available via the Download .thy links.

The deployed default site follows the current manifest on main. For a permanent
thesis snapshot, retain a versioned Pages copy before replacing commit-pinned
GitHub thesis links. Do not switch the thesis links until Pages is deployed and
verified. Existing thesis links remain unchanged by this site builder.
