#!/usr/bin/env python3
"""
Normalize generated Lean MLE lemmas.

Input:
  - A .lean file OR
  - A directory containing .lean files

Output:
  - New .lean files written to the SAME DIRECTORY AS THIS SCRIPT
  - Original filenames preserved
  - Original files are NOT modified

Transforms:
  map_f_to_bv_32 x  -> BVModEq.map_f_to_bv 32 x
  bool_to_bv_32 x   -> BVModEq.bool_to_bv 32 x
"""

from __future__ import annotations
import argparse
import re
from pathlib import Path


SCRIPT_DIR = Path(__file__).parent.resolve()


def normalize(text: str) -> str:
    # Ensure space after '=' when missing
    text = re.sub(r"=\s*(map_f_to_bv_32\b)", r"= \1", text)
    text = re.sub(r"=\s*(bool_to_bv_32\b)", r"= \1", text)

    # Rewrite only unqualified identifiers
    text = re.sub(
        r"(?<!\.)\bmap_f_to_bv_32\b",
        r"BVModEq.map_f_to_bv 32",
        text,
    )
    text = re.sub(
        r"(?<!\.)\bbool_to_bv_32\b",
        r"BVModEq.bool_to_bv 32",
        text,
    )

    # Cleanup
    text = re.sub(r"=  +", "= ", text)

    return text


def process_file(path: Path) -> None:
    src = path.read_text(encoding="utf-8")
    out = normalize(src)

    out_path = SCRIPT_DIR / path.name
    out_path.write_text(out, encoding="utf-8")

    print(f"[OK] {path.name} -> {out_path}")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument(
        "input",
        type=Path,
        help="A .lean file or a directory of .lean files",
    )
    args = ap.parse_args()

    inp: Path = args.input

    if inp.is_file():
        if inp.suffix != ".lean":
            raise SystemExit("Input file must be a .lean file")
        process_file(inp)

    elif inp.is_dir():
        lean_files = sorted(inp.glob("*.lean"))
        if not lean_files:
            print("[WARN] No .lean files found")
        for f in lean_files:
            process_file(f)

    else:
        raise SystemExit(f"Invalid input: {inp}")


if __name__ == "__main__":
    main()

