#!/usr/bin/env bash
set -euo pipefail

TARGET_DIR="${1:-.}"
OUT="${2:-lean_bench_results.csv}"

# --- detect timeout ---
if command -v timeout >/dev/null 2>&1; then TIMEOUT="timeout"
elif command -v gtimeout >/dev/null 2>&1; then TIMEOUT="gtimeout"
else echo "ERROR: install timeout"; exit 1
fi

# --- Find project root: accept lakefile.toml OR lakefile.lean ---
find_root() {
  local d="$PWD"
  while [[ "$d" != "/" ]]; do
    if [[ -f "$d/lakefile.toml" ]] || [[ -f "$d/lakefile.lean" ]]; then
      echo "$d"
      return 0
    fi
    d=$(dirname "$d")
  done
  return 1
}

PROJECT_ROOT=$(find_root || true)
if [[ -z "$PROJECT_ROOT" ]]; then
  echo "ERROR: Could not find Lake project root (lakefile.toml)."
  exit 1
fi

echo "[INFO] Project root: $PROJECT_ROOT"
LEAN_CMD="lake env lean"

mkdir -p errors
echo "file,time_seconds,status" > "$OUT"

# Prebuild dependencies once
(cd "$PROJECT_ROOT" && lake build >/dev/null 2>&1 || true)

# Expand Lean files
shopt -s nullglob
FILES=("$TARGET_DIR"/*.lean)

if [[ ${#FILES[@]} -eq 0 ]]; then
  echo "[WARN] No .lean files found inside $TARGET_DIR"
  exit 0
fi

echo "[INFO] Found ${#FILES[@]} files"

for f in "${FILES[@]}"; do
  fname=$(basename "$f")
  base="${fname%.lean}"
  errfile="errors/${base}.err"

  echo "[INFO] Checking $f"

  # Remove only this file’s olean
  olean="${f%.lean}.olean"
  [[ -f "$olean" ]] && rm -f "$olean"

  start=$(date +%s.%N)

  # Run Lean from project root for correct imports
  exitcode=0
  (
    cd "$PROJECT_ROOT"
    $TIMEOUT 60s $LEAN_CMD "$f" >"$errfile" 2>&1
  ) || exitcode=$?

  end=$(date +%s.%N)
  duration=$(echo "$end - $start" | bc)

  if [[ $exitcode -eq 0 ]]; then
    status="ok"
    [[ ! -s "$errfile" ]] && rm -f "$errfile"
  elif [[ $exitcode -eq 124 ]]; then
    status="timeout"
    cat "$errfile"
  else
    status="error"
    cat "$errfile"
  fi

  echo "$f,$duration,$status" >> "$OUT"
done

echo "[DONE] Results saved to $OUT"
