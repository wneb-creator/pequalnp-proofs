# Toolchain setup

The advertised warm environment was absent: no explicit ~/.pequalnp-prepared marker, no ~/.elan, and no lean/.lake. Installed the repository-pinned Lean v4.36.0 using the supported .github/scripts/install-elan.sh with elan v4.4.0 and SHA256 0e8250aa2be86c7af929ade68db617af9edc8b9ccf6eaf5ece228250d0d032e2 from the authoritative workflow.

Enable each command shell with:

```sh
. /tmp/oec/pequalnp-pilot-143/lean-env.sh
```

This sets the installed elan directory, the repo lake queue shim, and the scratch build queue directory. Run proof commands from lean/. The required initial lake exe cache get completed successfully (exit 0). Full install and cache stdout/stderr are retained under /tmp/oec/pequalnp-pilot-143/. No tracked project files were modified.
