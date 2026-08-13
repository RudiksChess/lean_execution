#!/usr/bin/env bash

# Prepare the complete Lean environment during Codespaces prebuilds. GitHub
# runs onCreateCommand while creating a prebuild, whereas postCreateCommand is
# deferred until a user opens the Codespace.
set -Eeuo pipefail

step() {
  printf '\n[%s] %s\n' "$(date -u +'%Y-%m-%dT%H:%M:%SZ')" "$*"
}

fail() {
  local exit_code=$?
  printf '\nCodespaces setup failed (exit %s). See the command output above.\n' "$exit_code" >&2
  exit "$exit_code"
}
trap fail ERR

if [[ ! -f lean-toolchain || ! -f lakefile.lean ]]; then
  printf 'Run this script from the repository root.\n' >&2
  exit 1
fi

readonly elan_dir="${ELAN_HOME:-${HOME}/.elan}"
export ELAN_HOME="$elan_dir"
export PATH="${elan_dir}/bin:${PATH}"

if [[ ! -x "${elan_dir}/bin/elan" ]]; then
  step "Installing elan"
  curl --proto '=https' --tlsv1.2 --fail --show-error --location \
    https://elan.lean-lang.org/elan-init.sh \
    | sh -s -- -y --no-modify-path
else
  step "elan is already installed; reusing it"
fi

lean_toolchain="$(<lean-toolchain)"
readonly lean_toolchain
if [[ -z "$lean_toolchain" ]]; then
  printf 'lean-toolchain is empty.\n' >&2
  exit 1
fi

toolchain_installed=false
while IFS= read -r installed_toolchain; do
  if [[ "${installed_toolchain%% *}" == "$lean_toolchain" ]]; then
    toolchain_installed=true
    break
  fi
done < <(elan toolchain list)

if [[ "$toolchain_installed" == true ]]; then
  step "Pinned Lean toolchain is already installed: ${lean_toolchain}"
else
  step "Installing pinned Lean toolchain: ${lean_toolchain}"
  elan toolchain install "$lean_toolchain"
fi

step "Downloading pinned Lake dependencies and compiled dependency cache"
lake exe cache get

step "Building this repository"
lake build

step "Building the independent Foundation cross-validation"
lake build Thesis.Prop.CompletenessViaFoundation

step "Lean environment is ready"
lean --version
lake --version
