#!/usr/bin/env python3
"""Print the key of the prebuilt dependency archive: the first 16 hex digits of the SHA-256 of
lean-toolchain followed by lake-manifest.json. A new toolchain or a new dependency pin needs a new archive."""
import hashlib, pathlib

root = pathlib.Path(__file__).resolve().parents[1]
h = hashlib.sha256()
for name in ('lean-toolchain', 'lake-manifest.json'):
    h.update((root / name).read_bytes())
print(h.hexdigest()[:16])
